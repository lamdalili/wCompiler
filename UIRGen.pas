unit UIRGen;

interface
uses
  Windows, SysUtils, Classes,Dialogs,Utils,UNodesBase,UTypes;
type
  TIRList=class(TQSObjList)
  private
    function GetItem(idx: integer): TCompNode;
  public
    property items[idx:integer]:TCompNode read GetItem;default;
  end;

  TStatec=(stUndefined,ssTrue,ssFalse);
  PStatecArray = ^TStatecArray;
  TStatecArray = array[0..0] of TStatec;
  TBitsSet=class
  private
    FCount:integer;
    FBits: PStatecArray;
    procedure CheckIndex(AIdx:integer);
    procedure SetBit(Index: Integer; Value: TStatec);
    function GetBit(Index: Integer): TStatec;
  public
    changed:boolean;
    constructor Create(ACount:integer);
    destructor Destroy; override;
    procedure ClearAll();
    procedure Fill(v:TStatec);
    procedure Copy(Src:TBitsSet);
    procedure InterSect(Src:TBitsSet);
    procedure Union(Src: TBitsSet);
    property Bits[Index: Integer]: TStatec read GetBit write SetBit; default;
    property Count: Integer read FCount;
  end;
  TGraphSection=class;
  TGraphRecClass=(grNone,grIfNode,grTry,grFinally,grTryEntry);
  TGraphRec=class
  private
    EndInsert:boolean;
    FIsJumpToJump:boolean;
    function GetIsJumpToJump: boolean;
  public
    UsedMark:boolean;
    FLabel:integer;
    FLinks:TGraphSection;
    FIRList:TIRList;
    LeftGraph:TGraphRec;
    RightGraph:TGraphRec;
    Vars_In_Set:TBitsSet;
    Vars_Out_Set:TBitsSet;
    Av_In_Set:TBitsSet;
    Av_Out_Set:TBitsSet;
    _Set:TBitsSet;
    constructor Create;
    destructor Destroy;override;
    procedure AddIRCode(AInst:TCompNode);
    property IsJumpToJump:boolean read GetIsJumpToJump;
  end;

  TGraphSection=class(TQSObjList)
  private
    function GetItem(idx: integer): TGraphRec;
  public
    procedure UnMarkAll;
    procedure BuildInterLinks();
    property items[idx:integer]:TGraphRec read GetItem;default;
  end;
function IRToString(IR:TCompNode): string;
implementation
uses typinfo,USymbolesTable,USynParser,UExtraNodes;

function IRName(ir:TQsCmdInst):string;
begin
  Result := Copy(GetEnumName(typeinfo(TQsCmdInst),ord(ir)),3,MAXINT);
end;

function ClassRefToStr(Expr:TExpr):string;
begin
  if Expr = nil then
  begin
    Result := '<null node>';
    Exit;
  end;
  Result :='unknown type ref';
  if Expr.DataType.IsMetaClass then
     Result := Expr.DataType.Dest.SymbInfo.Name;
end;
function ExprToStr(Expr:TExpr):string;
var
  Ex:TOprExpr;
begin
  if Expr = nil then
  begin
    Result := '<null node>';
    Exit;
  end;
  if Expr.DataType.IsMetaClass then
  begin
    Result := Expr.DataType.Dest.SymbInfo.Name;
    Exit;
  end;
  Ex:=TOprExpr(Expr);
  case Expr.xOp of
   imDeref :Result:='['+ExprToStr(Ex.Expr1)+']';
   imAddr :Result:='Addr '+ExprToStr(Ex.Expr1);
   imOffset:if Ex.Expr1.DataType.IsTypedPointer() then
               Result:='['+ExprToStr(Ex.Expr1)+' + '+ExprToStr(Ex.Expr2)+']'
             else
               Result:=ExprToStr(Ex.Expr1)+'[' +ExprToStr(Ex.Expr2)+']';//array /struct
    else
       case Expr.ObjLocation of
          olTemp: Result:= '_t'+inttostr(Expr.Address);
          olMem: Result:= '_p['+inttostr(Expr.Address)+']';
          olRet: Result:= '_result';
          olStatic,olAuto,
          olParam: Result:= Expr.Name;
          olLiteral,olCode:
                     Result:= FloatTostr(Expr.AsNumber) // for test
       else
          Result:= 'unknown('+InttoStr(Ord(Expr.ObjLocation))+')';
       end;
   end;
end;

function condStr(IR:TOprExpr):string;
var
 S:string;
 Opr,Labs:TOprExpr;
begin
  S:='';
  Opr :=TOprExpr(IR.Expr2);
  Labs :=TOprExpr(IR.Expr1);
  case Opr.xOp of
      imEqu:S:='==';
      imLess:S:='<';
      imGr:S:='>';
      imNotequ:S:='!=';
      imLessEqu:S:='<=';
      imGrEqu:S:='>=';
      imIs:S:='Is';
  end;
 { Result := '  _If('+ExprToStr(Opr.Expr1)+' '+S+' '
            +ExprToStr(Opr.Expr2)+') Goto '+ InttoStr(IR.Expr1.Value.vInt);  }

Result := '  _If('+ExprToStr(Opr.Expr1)+' '+S+' '+ExprToStr(Opr.Expr2)+')'
          +InttoStr(Labs.Expr1.Value.vInt)+':'+InttoStr(Labs.Expr2.Value.vInt);
                        ;
end;

function boolStr(IR:TOprExpr):string;
var
 Labs:TOprExpr;
begin
  Labs :=TOprExpr(IR.Expr1);
  Result := '  _If('+ExprToStr(IR.Expr2)+')'
            +InttoStr(Labs.Expr1.Value.vInt)+':'
            +InttoStr(Labs.Expr2.Value.vInt);
                        ;
end;

function oprstr(IR:TOprExpr):string;
var
 S:string;
 Opr:TOprExpr;
 tmp:TExpr;
begin
 Opr :=TOprExpr(IR.Expr2);
 tmp :=IR.Expr1;
 if Opr.Expr2 = nil then
    S :=IRName(Opr.xOp )+' '+ExprToStr(Opr.Expr1)
 else
    S :=ExprToStr(Opr.Expr1)+' '+IRName(Opr.xOp)+' '+ExprToStr(Opr.Expr2);
 Result :='  '+ExprToStr(tmp)+' ::= '+S;
end;

function DynCasrStr(Opr:TOprExpr):string;
begin
  if Opr = nil then
  begin
    Result := '<null node>';
    Exit;
  end;
  Result := ExprToStr(Opr.Expr1)+' ::= '+ExprToStr(Opr.Expr2)+' as '
               +Opr.Expr1.DataType.SymbInfo.Name;
end;

function CallToStr(Expr:TOprExpr):string;
var
  Ex:TOprExpr;
  fn:TFuncType;
  vs:string;
begin
  if Expr = nil then
  begin
    Result := '<null node>';
    Exit;
  end;
  Ex :=TOprExpr(Expr.Expr1);
  fn := TFuncType(Ex.Expr2.DataType);
  if Expr.Expr2 <> nil then
  begin
     vs:= Ex.Expr2.Name+' '+Inttostr(fn.VirtualOffset);
     if Expr.Expr2.DataType.IsInterface() then
        Result := 'iCall '+vs// call from interface
     else
        Result := 'vCall '+vs // virtual call
  end else begin
    // if Ex.Expr2.Name <>'' then
      //  Result := 'Call '+ Ex.Expr2.Name
    // else
        Result := 'Call '+ExprToStr(Ex.Expr2)
  end;
  if fn.FuncKind=mkClassMethod then
     Result := 'cls '+Result;

  if not Ex.Expr1.DataType.IsVoidType() then
     Result := ExprToStr(Ex.Expr1)+' ::= '+Result
end;

function GetIntrfEntryStr(IR:TOprExpr):string;
var
 Opr:TOprExpr;
begin
   Opr :=TOprExpr(IR.Expr2);
   Result :=ExprToStr(Opr.Expr1)+' : '+inttostr(TInterfaceType(IR.Expr1.DataType).IID);
end;

{ TIRRec }

function IRToString(IR:TCompNode): string;
var
 Opr:TOprExpr;
begin
  Result := IRName(IR.xOp);
  Opr :=TOprExpr(IR);
  case IR.xOp of
      ir_Inc,ir_Dec:
         Result :='  '+Result+'  '+ ExprToStr(Opr.Expr1)+' : '+ ExprToStr(Opr.Expr2);
      ir_Copy:
         Result := '  '+ExprToStr(Opr.Expr1)+' ::= '+ExprToStr(Opr.Expr2);
      ir_RelOp:
         Result :=condStr(Opr);
      ir_UnOp,ir_BinOp,ir_Addr:
         Result := oprstr(Opr);
      ir_IfFalse:
         Result :=boolStr(Opr);
      ir_GoTo:
         Result :='  '+Result+' '+ExprToStr(Opr.Expr1);
      ir_Print:
         Result :='  '+Result+' '+ExprToStr(Opr.Expr1);
      imConstructor:
         Result :='  '+ExprToStr(Opr.Expr1)+' ::= New '+ClassRefToStr(Opr.Expr2);
      ir_LoadParam :
             Result :='  '+Result+' '+ExprToStr(Opr.Expr1);
      ir_Call:
             Result :='  '+CallToStr(Opr);
      ir_DynamicCast:
             Result :='  '+DynCasrStr(Opr);
      ir_ErrRead:
             Result :='  '+ExprToStr(Opr.Expr1)+' ::= '+Result;
      ir_Throw:if Opr.Expr1 <> nil then
                  Result :='  '+Result+'  '+ExprToStr(Opr.Expr1)
               else
                  Result :='  '+Result;
      ir_TryEnter,ir_ExitFinally,ir_ExitExcept,ir_ExceptRet,
      ir_FinallyRet:
               Result :='  '+Result;
  end;
end;

{ TIRList }

function TIRList.GetItem(idx: integer): TCompNode;
begin
   Result := TCompNode(inherited GetItem(idx));
end;

{ TGraphRec }

procedure TGraphRec.AddIRCode(AInst: TCompNode);
begin
   if EndInsert then
      raise ECompException.Create('AddIRCode insert error');
   FIsJumpToJump:=(AInst.xOp=ir_GoTo)and(FIRList.Count=0);
   FIRList.Add(AInst);                                              //  ir_ExitExcept
   EndInsert := AInst.xOp in [ir_IfFalse,ir_GoTo];
end;

constructor TGraphRec.Create;
begin
    FLinks:=TGraphSection.Create;
    FIRList:=TIRList.Create;
end;

destructor TGraphRec.Destroy;
begin
  FLinks.Free;
  FIRList.Free;
  inherited;
end;

function TGraphRec.GetIsJumpToJump: boolean;
begin
  Result :=(LeftGraph<>nil) and(  FIsJumpToJump or (FIRList.Count=0) );
end;

{ TGraphList }

procedure TGraphSection.BuildInterLinks;
var
 I:integer;
 Grf:TGraphRec;
begin
  for i:= 0 to Count-1 do
    Items[I].FLinks.Clear();
  for i:= 0 to Count-1 do
  begin
    Grf :=Items[I];
    if Grf.LeftGraph <>nil then
       Grf.LeftGraph.FLinks.Add(Grf);
    if Grf.RightGraph <>nil then
       Grf.RightGraph.FLinks.Add(Grf);
  end;
end;

function TGraphSection.GetItem(idx: integer): TGraphRec;
begin
   Result :=TGraphRec(inherited GetItem(idx));;
end;

procedure TGraphSection.UnMarkAll();
var
 I:integer;
begin
  for i:= 0 to Count-1 do
    Items[I].UsedMark:=False;
end;


{ TBitsSet2 }

procedure TBitsSet.CheckIndex(AIdx: integer);
begin
   if (AIdx < 0)or (AIdx >=FCount)then
     raise ECompException.CreateFmt('index out of bits range %d',[AIdx]);
end;

procedure TBitsSet.ClearAll;
begin
  FillChar(FBits^,FCount , 0);
end;

procedure TBitsSet.Copy(Src: TBitsSet);
var
 I:integer;
begin
 for I:= 0 to FCount-1 do
     Bits[I]:=Src[I];
end;

constructor TBitsSet.Create(ACount: integer);
begin
   if ACount < 0 then
      raise ECompException.Create('neg size TIdSet.Create');
   GetMem(FBits,ACount);
   FillChar(FBits^,ACount , 0);
   FCount:=ACount;
end;

destructor TBitsSet.Destroy;
begin
  FreeMem(FBits,FCount);
  inherited;
end;

function TBitsSet.GetBit(Index: Integer): TStatec;
begin
   CheckIndex(Index);
   Result :=FBits[Index];
end;

procedure TBitsSet.SetBit(Index: Integer; Value: TStatec);
begin
   CheckIndex(Index);
   if FBits[Index] <>Value then
      changed :=True;
   FBits[Index]:=Value;
end;

procedure TBitsSet.Fill(v: TStatec);
var
 I:integer;
begin
 for I:= 0 to FCount-1 do
   FBits^[I]:=v;
end;

procedure TBitsSet.InterSect(Src: TBitsSet);
var
 i:integer;
begin
  for I :=0 to Count -1 do
  begin
     if Src.Bits[i]= stUndefined then
        continue;
     if (Src.Bits[I]=ssFalse)or(Bits[i]=ssFalse)then
        Bits[I]:= ssFalse
     else
        Bits[I]:= ssTrue
  end;
end;

procedure TBitsSet.Union(Src: TBitsSet);
var
 i:integer;
begin
  for I :=0 to Count -1 do
  begin
     if Src.Bits[i]= ssTrue then
        Bits[I]:= ssTrue
  end;
end;
end.
