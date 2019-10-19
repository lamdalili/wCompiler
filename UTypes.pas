unit UTypes;

interface
uses
   SysUtils,UNodesBase;

type

  TArrayType=class(TDataType)
  private
    FCount:integer;
    procedure SetCount(Value:integer);
  public
    IndexType:TDataType;
    property Count:integer read FCount write SetCount;
  end;

  TTypeMembers=class(TDataType)
  public
    Members: TExprList;
    constructor Create();override;
    destructor Destroy();override;
  end;

  TFuncType=class(TTypeMembers)
  public
    FuncKind:(mkStaticFunc,mkMethod,mkClassMethod);
    VirtualOffset:integer; // index
    function IsEqual(AFunc:TDataType):boolean;
    function IsSignatureEqual(AFunc:TDataType;AQualifier:boolean):boolean;
    function ParamsNamesEqual(AFunc: TDataType): boolean;
  end;

  TBitField= class(TDataType)
  public
    BitsOffset:integer;
    BitsCount:integer;
  end;
 
  TClassType=class(TTypeMembers)
  public
    Instance_Size:integer;
    function IsInstanceOf(AType:TDataType):boolean;
    function Support(AIntrfType:TDataType):boolean;
  end;

  TInterfaceType=class(TTypeMembers)
  public
    IID:integer;
    Table_Size:integer;
  end;
function SelectIntType(AValue:int64):TExpr;
function SelectSubIntType(AIntType:TDataType):TExpr;
function AlignNum(AValue:integer):integer;
function AlignByUnit(AValue:integer):integer;
function ValueSize(FirstValue,LastValue:Extended;var Signed:boolean):integer; overload;
function UnSignedValueSize(value:Extended):integer;
function SignedValueSize(value:Extended):integer;
function SelectSignedIntType(AIntType:TDataType):TExpr;
function IsTypeEqual(t1,t2:TDataType): boolean;
var
   VoidType  :TExpr;
   CharType  :TExpr;
   ShortType :TExpr;
   IntType   :TExpr;
   ByteType  :TExpr;
   SByteType :TExpr;
   UShortType:TExpr;
   UIntType  :TExpr;
   BoolType  :TExpr;
   FloatType :TExpr;
   PtrType   :TExpr;
   IntrfType :TExpr;
implementation
uses UMsg,USymbolesTable,Utils;

function AlignNum(AValue:integer):integer;
begin
    Result := ((AValue + ALIGN_SIZE -1)div ALIGN_SIZE) * ALIGN_SIZE;
end;

function AlignByUnit(AValue:integer):integer;
begin
    Result := ((AValue + ALLOC_UNIT -1)div ALLOC_UNIT) ;
end;

function SignedValueSize(value:Extended):integer;
begin
   if value < 0 then
      value:= - value-1;
   if value < 128 then
      Result:= 1
   else if value < 32768 then
      Result:= 2
   else if value < 2147483648 then
      Result:= 4
   else
      Result:= 8
end;

function UnSignedValueSize(value:Extended):integer;
begin
   if value < 256 then
      Result:= 1
   else if value < 65536 then
      Result:= 2
   else if value < 4294967296 then
      Result:= 4
   else
      Result:= 8
end;

function ValueSize(FirstValue,LastValue:Extended;var Signed:boolean):integer;
var
 abs1,abs2:Extended;
 Signed1,Signed2:boolean;
begin
   Signed1 :=FirstValue < 0;
   Signed2 :=LastValue < 0;
   Signed := Signed1 or Signed2;
   if Signed1 xor Signed2 then
   begin
       abs1:=LastValue; if Signed2 then abs1:= - LastValue-1;
       abs2:=FirstValue;if Signed1 then abs2:= - FirstValue-1;
       if abs1 < abs2 then
          abs1:=abs2;
       Result := SignedValueSize(abs1)
   end else if Signed1 then   // Signed1 and Signed2
       Result := SignedValueSize(FirstValue)
   else          // not Signed1 and not Signed2
       Result := UnSignedValueSize(LastValue)
end;

function SelectIntType(AValue:int64):TExpr;
var
  Signed:boolean;
  Sz:integer;
begin
   Sz := ValueSize(AValue,AValue,Signed);
   Result :=nil;
   if Signed then
     case Sz of
       1: Result := SByteType;
       2: Result := ShortType;
       4: Result := IntType;
     end
   else
     case Sz of
       1: Result := ByteType;
       2: Result := UShortType;
       4: Result := UIntType;
     end;
   if Result =nil then
      raise ECompException.CreateRes(@INVALIDTYPE);
end;

function SelectSubIntType(AIntType:TDataType):TExpr;
begin
   with AIntType do
   begin
       if TypeClass<>tcInteger then
          raise ECompException.CreateRes(@INVALIDTYPE);
       Result :=nil;
       if itSigned in BitsClass  then
       begin
          if it32Bit in BitsClass then Result := IntType
          else if it16Bit in BitsClass then Result := ShortType
          else if it8Bit  in BitsClass then Result := SByteType;
       end else begin
          if it32Bit in BitsClass then Result := IntType
          else if it16Bit in BitsClass then Result := UShortType
          else if it8Bit  in BitsClass then Result := ByteType;
       end;
       if Result = nil then
          raise ECompException.CreateRes(@INVALIDTYPE);
   end;
end;

function SelectSignedIntType(AIntType:TDataType):TExpr;
begin
   with AIntType do
   begin
       if TypeClass<>tcInteger then
          raise ECompException.CreateRes(@INVALIDTYPE);
       Result :=nil;
       if not (itSigned in BitsClass)  then
       begin
          if it32Bit in BitsClass then Result := IntType
          else if it16Bit in BitsClass then Result := IntType  //ShortType
          else if it8Bit  in BitsClass then Result := ShortType; //SByteType
       end
         else Result :=AIntType.SymbInfo;

       if Result = nil then
          raise ECompException.CreateRes(@INVALIDTYPE);
   end;
end;

{ TFuncType }

function IsTypeEqual(t1,t2:TDataType): boolean;
begin
    Result := False;
    if t1 = t2 then
       Result := True
    else begin
       if t1.TypeClass = t2.TypeClass then
       case t1.TypeClass of
            tcChar,tcFloat,tcBool:Result := True;
               tcEnum:Result := t1=t2;
            tcInteger:Result := t1.BitsClass = t2.BitsClass;
            tcArray,tcPointer,tcClassRef:begin
                  Result := t1.Dest = t2.Dest;
             end;
        end;
    end;
end;

function TFuncType.ParamsNamesEqual(AFunc: TDataType): boolean;
var
 I:integer;
 Name1,Name2:string;
begin
   Result :=False;
   if(AFunc.TypeClass<>tcFuncType)
      or(Members.Count<>TFuncType(AFunc).Members.Count)then
         Exit;
   for I:=0 to Members.Count-1 do
    with TFuncType(AFunc).Members do
    begin
       Name1 := TSymIdent(Members.GetExpr(i)).Name;
       Name2 := TSymIdent(GetExpr(i)).Name;
       if not SameText(Name1,Name2) then
          Exit;
    end;
    Result := True;
end;

function TFuncType.IsSignatureEqual(AFunc: TDataType;AQualifier:boolean): boolean;
var
 I:integer;
 ex1,ex2:TExpr;
begin
   Result :=False;
   if (AFunc.TypeClass<>tcFuncType)or(TFuncType(AFunc).Members.Count<>Members.Count) then
      Exit;
   for I:= 0 to  Members.Count-1 do
   begin
      ex1:=Members.GetExpr(i);
      ex2:=TFuncType(AFunc).Members.GetExpr(i);
      if (AQualifier and(ex1.QureyKind<>ex2.QureyKind))
         or not IsTypeEqual(ex1.DataType,ex2.DataType) then
            Exit;
   end;
   Result := True;
end;

function TFuncType.IsEqual(AFunc: TDataType): boolean;
begin
   Result := IsTypeEqual(Dest,AFunc.Dest)
             and IsSignatureEqual(AFunc,True)
             and (FuncKind= TFuncType(AFunc).FuncKind);
end;

{ TTypeMembers }

constructor TTypeMembers.Create;
begin
   inherited;
   Members :=TExprList.Create;
end;

destructor TTypeMembers.Destroy;
begin
  Members.Free;
  inherited;
end;

function MakeBaseType(ATypeClass:TTypeClass;Bits:TBitsClass;ASize:integer;
      ADest:TDataType):TSymIdent;
var
 D:TDataType;
begin
    Result :=TSymIdent.Create;
    Result.ObjLocation := olType;
    D:=TDataType.Create;
    Result.SetDataType(D);
    D.SymbInfo :=Result;
    D.SeBaseTypeProps(ATypeClass,Bits,ASize,ADest);
end;

function MakeBaseInterface():TSymIdent;
var
 D:TDataType;
begin
    Result :=TSymIdent.Create;
    Result.ObjLocation := olType;
    D:=TInterfaceType.Create;
    Result.SetDataType(D);
    D.SymbInfo :=Result;
    D.SeBaseTypeProps(tcInterface,[],SIZEOFPOINTER,nil);
end;
{ TArrayType }

procedure TArrayType.SetCount(Value: integer);
begin
   if Dest =nil then
      raise ECompException.CreateRes(@INVALIDTYPE);
   FCount := Value;
   TypeSize := Value * Dest.TypeSize;
end;

{ TClassType }

function TClassType.IsInstanceOf(AType: TDataType): boolean;
begin
  Result := AType.IsClass()and( (Self=AType)
            or TClassStmt(SymbInfo).IsInheritedFrom(TClassStmt(AType.SymbInfo)))
end;

function TClassType.Support(AIntrfType: TDataType): boolean;
var
  C:TIntrfImplementation;
begin
  Result :=AIntrfType.IsInterface()
           and TClassStmt(SymbInfo).Support(AIntrfType,C)
end;

begin
   ByteType  := MakeBaseType(tcInteger,[it8bit],1,nil);
   UShortType:= MakeBaseType(tcInteger,[it8bit,it16bit],2,nil);
   UIntType  := MakeBaseType(tcInteger,[it8bit,it16bit,it32bit],4,nil);
   SByteType := MakeBaseType(tcInteger,[itSigned,it8bit],1,nil);
   ShortType := MakeBaseType(tcInteger,[itSigned,it8bit,it16bit],2,nil);
   IntType   := MakeBaseType(tcInteger,[itSigned,it8bit,it16bit,it32bit],4,nil);

   BoolType  := MakeBaseType(tcBool, [],1,nil);
   FloatType := MakeBaseType(tcFloat,[],4,nil);
   VoidType  := MakeBaseType(tcVoid, [],0,nil);
   CharType  := MakeBaseType(tcChar, [],1,nil);
   PtrType   := MakeBaseType(tcPointer, [],4,VoidType.DataType);
   IntrfType := MakeBaseInterface();
end.
