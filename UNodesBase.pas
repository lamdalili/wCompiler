unit UNodesBase;

interface
uses
    SysUtils,Classes,Utils;
const
    ALLOC_UNIT = 8; //bits
    INT_UNIT  =  4;
    ALIGN_UNIT  =  ALLOC_UNIT * 1;
    
    SIZEOFPOINTER = 4;
    ALIGN_SIZE = 4;
    RETOURADDR_RECT = 4;
    FRAMEPTR_RETOURADDR_RECT = 8;

    IUNKNOWN_INTF_IID = $00000001;
type

  TTypeClass  =(tcNone,tcInteger,tcChar,tcPointer,tcBool,tcVoid,tcFloat,
                tcFuncType,tcArray,tcStruct,tcEnum,tcClass,tcInterface,tcClassRef);
  TBitsClass = set of (itSigned,it8Bit,it16Bit,it32Bit,itBitField);
  TTypeClasSet=set of TTypeClass;

  TVisLevel   =(vsPrivate,vsPublic,vsProtected,vsLocalProtected,vsLocal);
  TQureyKind  =(atValue,atReference);
  TAccessType =(qoReadWrite,qoReadOnly,qoWriteOnly);
  TObjLocation=(olNone,olType,olStatic,olAuto,olField,
                  olParam,olRet,olMem,
                  olLiteral,olCode, olLabel,
                  olTemp);    //
  TQsCmdInst=(imNone,
    imValue,imSymb,imTextStream,imInitList,
    imMinus,imPlus,imNot,imComp,imAddr,imDeref,
    imPreInc,imPreDec,imPostInc,imPostDec,
    imAdd,imSub,imMul,imDiv,imModul,
    imAnd,imOr,imXor,imShl,imShr,
    imEqu,imLess,imGr,imNotequ,imLessEqu,imGrEqu,imIs,imAs,
    imOrCmp,imAndCmp,imTest,
    imAssign,imInvocation,imFuncEpilogue,
    __NodeTypeConvert,// :convertion type
    imImplicit,imExplicit,
    imOffset,imRef,imBase,imInstance,
    imExprInitStmt,imBlockStmt,imPrintStmt,imConstructor,
    imEmptyStmt,imExprStmt,imIfStmt,imWhileStmt,imDoStmt,imForStmt,
    imListStmt,imGoToStmt,imLabelStmt,imReturnStmt,imBreakStmt,
    imContinueStmt,imSwitchStmt,imFinallyStmt,imCatchStmt,imThrowStmt,
    
    // IR nodes
    __TryEnd,__TrySecLink,// for graph optimization
    ir_TryEnter,ir_ExitFinally,ir_ExitExcept,ir_FinallyRet,
    ir_Throw,ir_ExceptRet,ir_ErrRead,ir_POPErr,
    ir_Inc,ir_Dec,ir_Copy,ir_Print,
    ir_LoadParam,ir_RelOp,ir_BinOp,ir_UnOp,ir_Addr,
    ir_GoTo,ir_Ret,ir_Call,
    ir_IfFalse,ir_DynamicCast
    // get interface from class or interface
    );
  TDclModifier = (dmNone,dmInline,
                  dmPrivate,dmProtected,dmLocal,dmLocalProtected,dmPublic,// do not change order
                  dmNew,dmVirtual,dmOverride,dmAbstract,
                  dmBitField,dmOpenArray,
                  dmPtrDcl,dmArrayDcl,
                  dmVoidDcl,dmAbstractDcl,
                  dmTypeRequired,
                  dmStatic,dmReadonly,dmAuto,dmField,dmClassMthd,
                  dmInitOptional,dmMustInit,
                  dmFuncForward,dmFuncDcl,
                  dmExtentedType,
                  dmCtrlStmts,
                  dmInitializer);
  TDclModifiers = set of  TDclModifier;
  TNodeBase =class
  public
    Line:integer;
  end;

  TCompNode =class(TNodeBase)
  public
    xOp:TQsCmdInst;
  end;

  TExpr=class;
  TDataType=class
  private
    procedure Calc_Bounds;
  public
    TypeClass:TTypeClass;
    TypeSize:integer;
    BitsClass:TBitsClass;
    Dest:TDataType; //array ant pointers
    SymbInfo :TExpr;
    Max_Range:Extended;
    Min_Range:Extended;
    constructor Create();virtual;
    procedure SeBaseTypeProps(ATypeClass:TTypeClass;Bits: TBitsClass;
              ASize:integer;ADest:TDataType);
    function IsBool: boolean;
    function IsIntType():boolean;
    function IsVoidType():boolean;
    function IsFuncType():boolean;
    function IsNumericType():boolean;
    function IsFloatType():boolean;
    function IsOrdinalType: boolean;
    function IsArray: boolean;
    function IsRangeType: boolean;
    function IsTypedPointer: boolean;
    function IsExtentedType: boolean;
    function IsPointer: boolean;
    function IsOpenArray: boolean;
    function IsUnTypedPointer: boolean;
    function IsBitsFieldType: boolean;
    function IsCharArray: boolean;
    function IsStructArrayType: boolean;
    function IsMethodType():boolean;
    function IsClass():boolean;
    function IsMetaClass():boolean;
    function IsInterface: boolean;
    function IsClsIntrfType:boolean;
  end;
  PValueExpr =^TValueExpr;
  TValueExpr=record
     case integer of
       1:(vInt:integer);
       2:(vShort:smallint);
       3:(vSByte:shortint);
       4:(vUInt:cardinal);
       5:(vUShort:word);
       6:(vByte:byte);
       7:(vInt64:int64);
       8:(vFloat:Extended);
       9:(vPtr  :Pointer);
      10:(vBool :boolean);
      11:(vChar :Char);
  end;

  TExpr= class(TCompNode)
  private
    function Init: PValueExpr;
    function GetNumber: Extended;
    function GetInteger: integer;
    function GetString: string;
  protected
    FDataType:TDataType;
    FValue: TValueExpr;
    FName:string;
    function GetDataType: TDataType;
  public
    ObjLocation:TObjLocation;
    AccessType :TAccessType;
    QureyKind :TQureyKind;
    Address : integer;
    Used:boolean;
  public
    property Name:string read FName write FName;
    procedure SetDataType(const Value: TDataType);virtual;
    property DataType:TDataType read GetDataType write SetDataType;
    function IsVariable():boolean;
    function IsLValue():boolean;
    function IsRValue: boolean;
    function IsConstant():boolean;
    function IsAddressable():boolean;
    function IsReadOnly():boolean;
    function IsField():boolean;
    function IsMethod():boolean;
    function IsClassMethod():boolean;
    function IsType():boolean;
    function IsCode: boolean;
    function IsBlockVar(): boolean;
    procedure Assign(ASource:TExpr);
    function ExpectLValue():TExpr;
    function ExpectRValue():TExpr;
    procedure ExpectBooleanExpr;
    procedure ExpectConditionExpr;
    property Value:pValueExpr read Init;
    property AsNumber:Extended read GetNumber;
    property AsInteger:integer read GetInteger;
    property AsString:string read GetString;
    function HasType():boolean;
    procedure Afterconstruction();override;
  end;

 // TExpr =TExpr;

  TSymbolExpr =class(TExpr)
  protected
    FVisibility:TVisLevel;
  //  FName:string;
  public
  //  property Name:string read FName write FName;
    property Visibility:TVisLevel read FVisibility write FVisibility;
   
  end;

   TLoopStmt =class;
   
   TStmt=class(TCompNode)
   public
     StartLab,EndLab:integer;
     StmtsJumps:TLoopStmt;
     constructor Create;virtual;
   end;
   TStmtClass = class of TStmt;

   TLoopStmt=class(TStmt)
   public
      ContinueLab,BreakLab:integer;
   end;
   TLoopStmtClass = class of TLoopStmt;

    TExprList =class(TQSObjList)
    public
      function AddExpr(AExpr:TExpr):integer;
      function GetExpr(AIndex:integer):TExpr;
    end;

    TStmtList =class(TStmt)
    protected
      FList:TQSList;
    public
      constructor Create;override;
      destructor Destroy; override;
      property List:TQSList read FList;
    end;


implementation
uses UTypes,UMsg,Math,UCommon;

procedure TExpr.Afterconstruction;
begin
  inherited;
  Address :=-1;
end;

function TExpr.IsAddressable: boolean;
begin
   Result := (ObjLocation in [olStatic,olMem,olAuto,olParam,olCode,olRet])
              and not (itBitField in DataType.BitsClass)
             // and not DataType.IsMethodType;
end;

function TExpr.IsConstant: boolean;
begin
  Result := (ObjLocation in [olLiteral,olCode,olLabel])
             and (not DataType.IsMethodType);
end;

function TExpr.IsReadOnly: boolean;
begin
  Result := IsAddressable() and (AccessType = qoReadOnly);
end;

function TExpr.IsVariable: boolean;
begin
  Result := (ObjLocation in [olStatic,olMem,olAuto,olTemp,olParam,olRet]);
end;

function TExpr.IsLValue: boolean;
begin
  Result := (ObjLocation in [olStatic,olMem,olAuto,olParam,olRet])
            and (AccessType <> qoReadOnly)
            and not(DataType.TypeClass in [tcVoid,tcArray,tcStruct]);// 
end;

function TExpr.IsRValue: boolean;
begin
  Result := ObjLocation in [olStatic,olAuto,olParam,olLiteral,
                            olTemp,olRet,olMem,olCode]
end;

function TExpr.IsType: boolean;
begin
  Result := ObjLocation = olType;
end;

function TExpr.IsField: boolean;
begin
  Result := ObjLocation = olField;// for test
end;

{ TDataType }

constructor TDataType.Create;
begin
end;

function TDataType.IsCharArray: boolean;
begin
  Result := (TypeClass=tcArray)and(Dest.TypeClass=tcChar)
end;

function TDataType.IsTypedPointer: boolean;
begin
   Result := (TypeClass=tcPointer)
              and (Dest.TypeClass <> tcVoid) ;
end;

procedure TDataType.Calc_Bounds();
begin
    case TypeClass of
      tcInteger,tcChar,tcEnum:
            if itSigned in BitsClass then
            begin
               Min_Range := -int64((int64(1) shl (TypeSize * ALLOC_UNIT )) div 2);
               Max_Range :=  int64((int64(1) shl (TypeSize * ALLOC_UNIT )) div 2)-1
            end else begin
               Min_Range :=  0;
               Max_Range := (int64(1) shl (TypeSize * ALLOC_UNIT ))-1;
            end;
      tcFloat:begin
               Min_Range := -MaxExtended;
               Max_Range :=  MaxExtended;
            end;
    else
       raise ECompException.CreateRes(@INT_TYPE_REQUIRED);
    end;
end;

function TDataType.IsFuncType: boolean;
begin
    Result := TypeClass = tcFuncType;
end;

function TDataType.IsIntType: boolean;
begin
    Result := TypeClass = tcInteger;
end;

function TDataType.IsNumericType: boolean;
begin
    Result :=  IsIntType or IsFloatType
end;

function TDataType.IsFloatType: boolean;
begin
   Result :=  TypeClass=tcFloat
end;

function TDataType.IsOrdinalType: boolean;
begin
    Result :=  TypeClass in [tcInteger,tcChar,tcEnum];
end;

function TDataType.IsRangeType: boolean;
begin
   Result :=  TypeClass in [tcInteger,tcChar,tcEnum,tcFloat];
end;

function TDataType.IsExtentedType: boolean;
begin
   Result :=  TypeClass in [tcFuncType,tcArray,tcStruct,tcEnum];
end;

function TDataType.IsVoidType: boolean;
begin
   Result := TypeClass in [tcVoid];
end;

procedure TDataType.SeBaseTypeProps(ATypeClass: TTypeClass;
  Bits: TBitsClass; ASize: integer; ADest: TDataType);
begin
  TypeSize :=ASize;
  BitsClass :=Bits;
  Dest:=ADest;
  TypeClass :=ATypeClass;
  if IsRangeType then
     Calc_Bounds();
end;

function TDataType.IsOpenArray: boolean;
begin
  if TypeClass=tcArray then
  begin
     if Dest.TypeClass= tcArray then
        Result := Dest.IsOpenArray
     else
        Result := TArrayType(Self).Count = 0
  end else begin
      Result :=False;
  end;

end;

function TDataType.IsBool: boolean;
begin
  Result := TypeClass=tcBool ;
end;

function TDataType.IsUnTypedPointer: boolean;
begin
   Result := (TypeClass=tcPointer)and (Dest.TypeClass = tcVoid);
end;

function TDataType.IsPointer: boolean;
begin
   Result := TypeClass=tcPointer ;
end;

function TDataType.IsArray: boolean;
begin
   Result := TypeClass=tcArray;
end;

function TDataType.IsBitsFieldType: boolean;
begin
  Result := itBitField  in BitsClass;
end;

function TDataType.IsStructArrayType: boolean;
begin
    Result := TypeClass in [tcArray,tcStruct] ;
end;


function TDataType.IsMethodType: boolean;
begin
    Result := (TypeClass=tcFuncType)and(TFuncType(Self).FuncKind<> mkStaticFunc)
end;

function TDataType.IsClass: boolean;
begin
    Result := TypeClass = tcClass;
end;

function TDataType.IsInterface: boolean;
begin
    Result := TypeClass = tcInterface;
end;
function TDataType.IsClsIntrfType: boolean;
begin
   Result := TypeClass in [tcClass,tcInterface];
end;

function TDataType.IsMetaClass: boolean;
begin
  Result := TypeClass=tcClassRef;
end;

{ TExprList }

function TExprList.AddExpr(AExpr: TExpr): integer;
begin
  Result := Add(AExpr);
end;

function TExprList.GetExpr(AIndex: integer): TExpr;
begin
  Result := TExpr(GetItem(AIndex));
end;

constructor TStmtList.Create;
begin
   inherited;
   Flist := TQSList.Create;
end;

destructor TStmtList.Destroy;
begin
  Flist.Free;
  inherited;
end;

{ TSymbolExpr }

function TExpr.GetDataType: TDataType;
begin
   if FDataType = nil then
     raise ECompException.Create('invalid type');
   Result := FDataType;
end;

procedure TExpr.SetDataType(const Value: TDataType);
begin
   FDataType :=Value;
end;

{ TStmt }

constructor TStmt.Create;
begin
end;

procedure TExpr.Assign(ASource: TExpr);
begin
    ObjLocation:=ASource.ObjLocation;
    AccessType :=ASource.AccessType;
    Line       :=ASource.Line;
    FValue     :=ASource.FValue;
    Address    :=ASource.Address;
    FName      :=ASource.FName;
    FDataType  :=ASource.FDataType;
    Address      :=ASource.Address;
    QureyKind  :=ASource.QureyKind;
end;

function TExpr.IsCode: boolean;
begin
   Result := ObjLocation in [olCode];
end;

function TExpr.IsBlockVar: boolean;     ///olRet,olAuto,olTemp,olParam
begin
   Result := ObjLocation in [olAuto,olParam,olTemp];
end;

function TExpr.HasType: boolean;
begin
   Result := FDatatype<> nil
end;

function TExpr.ExpectLValue: TExpr;
begin
   if not IsLValue then
      raise ECompException.CreateRes(@LVALUE_EXPECTED);
   Result := Self;
end;

procedure TExpr.ExpectBooleanExpr;
begin
   if not Datatype.IsBool then
      raise ECompException.CreateRes(@BOOL_EXPR_EXPECTED);
end;

function TExpr.Init: PValueExpr;
begin
   Result :=@FValue;
end;

procedure TExpr.ExpectConditionExpr;
begin
   if (not Datatype.IsBool) then//and(not isPointer)
      raise ECompException.CreateRes(@COND_EXPECTED);
end;

function TExpr.GetNumber: Extended;
begin
  if DataType.TypeClass = tcFloat then
     Result := FValue.vFloat
  else
     Result := AsInteger;
end;

function TExpr.GetInteger: integer;
begin
  with DataType do
  if TypeClass = tcFloat then
  begin
     Result := Int64(Trunc(FValue.vFloat));
  end else begin
       if itSigned in  BitsClass  then
       begin
          if it32Bit in BitsClass then Result :=  FValue.vInt
          else if it16Bit in BitsClass then Result := FValue.vShort
          else Result := FValue.vSByte;
       end else begin
          if it32Bit in BitsClass then Result :=  FValue.vUInt
          else if it16Bit in BitsClass then Result := FValue.vUShort
          else Result := FValue.vByte;
       end;
  end;
end;

function TExpr.GetString: string;
var
  St:TResBucket;
  C:Char;
  I:integer;
begin
   Result :='';
   if DataType.TypeClass=tcChar then
      Result := FValue.vChar
   else if DataType.IsCharArray() then
      if TObject(FValue.vPtr) is TResBucket then
      begin
          St := FValue.vPtr;
          for I:= 0 to TArrayType(DataType).Count-1 do
          begin
             C:=Chr(St.Data[I]);
             if C=#0 then
                break;
             Result:=Result+C;
          end;
      end;
end;

function TExpr.IsMethod: boolean;
begin
 Result := (ObjLocation = olCode) and ((DataType as TFunctype).FuncKind<>mkStaticFunc);
end;

function TExpr.ExpectRValue: TExpr;
begin
    if not IsRValue() then
        raise ECompException.CreateRes(@RVALUE_EXPECTED);
    Result := Self;
end;

function TExpr.IsClassMethod: boolean;
begin
  Result := (ObjLocation = olCode) and ((DataType as TFunctype).FuncKind=mkClassMethod);
end;

end.
