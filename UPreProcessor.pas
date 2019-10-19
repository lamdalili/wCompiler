unit UPreProcessor;

interface
uses SysUtils,classes, ULexParser,Utils,USynParser,UTypes,
     dialogs;

type

  TMsgClass =(msNone,msError,msWarning,msNote);
  TPreProcessor=class;
  TMsgRec=class
  private
    index:integer;
  public
    sMgsType: TMsgClass;
    sLine   : integer;
    sArg    : string;
    sData   : TObject;
  end;

  TMsgsList=class(TList)
  private
    function GetItem(index: integer): TMsgRec;
  public
    property Items[index:integer]:TMsgRec read GetItem; default;
  end;

  TPreProcessor=class(TSynParser)
  private
    __errindex:integer;
    FDefineList:TStringList;
    FTokensList:TPDataDynArray;
    NewCount:integer;
    function ppCondition_Block(ASkip: boolean):boolean;
    function ppParantExpr: integer;
    function ppPrimaryExpr(AMove,ARequired: boolean):integer;
    function ppRelationalExpr(AMove:boolean):integer;
    function ppEqualityExpr(AMove:boolean):integer;
    function ppBooleanExpr(AMove:boolean):integer;
    procedure ppIfDef_Stmt(ASkip: boolean);
    procedure ppIf_Section(ATest,ASkip: boolean);
    procedure ppIfNDef_Stmt(ASkip: boolean);
    procedure ppDefine_Stmt();
    procedure ppUnDefine_Stmt();
    procedure ppWrning_Stmt();
    procedure ppError_Stmt();
    procedure ppIf_Stmt(ASkip:boolean);
    procedure Section_Block(ASkip,AMove: boolean);
    procedure DelDefine(const AName:string);
    function GetDefine(const AName:string):integer;
    function GetLineTxt():string;
    procedure AddCurrenToken;
  protected
    FErrorsCount:integer;
    FfreeList:TQSObjList;
    FMsgsList:TMsgsList;
    FName:string;
  public
    Data:Pointer;
    constructor Create();
    destructor Destroy();override;
    function Parse(const ACode:string):integer;override;
    property MsgsList:TMsgsList read FMsgsList;
    property ErrorsCount:integer read FErrorsCount;
    procedure ExportMsgs(AList:TStrings);
    procedure Msg_Report(AMgsType:TMsgClass;ARes:PResStringRec);overload;
    procedure Msg_Report(AMgsType:TMsgClass;const Arg:string);overload;
    procedure Msg_Report(AMgsType: TMsgClass; const Arg: string;ALine: integer);overload;
    property Name:string read FName;
  end;
implementation
uses UMsg;
{ TPreProcessor }
constructor TPreProcessor.Create;
begin
  FDefineList:=TStringList.Create;
  FDefineList.Duplicates :=dupIgnore;
  FDefineList.Sorted:=True;
  FfreeList:=TQSObjList.Create;
  FfreeList.OwnObjs:=True;
  FMsgsList:=TMsgsList.Create;
end;

destructor TPreProcessor.Destroy;
begin
  FMsgsList.Free;
  FDefineList.Free;
  FfreeList.Free;
  inherited;
end;

function TPreProcessor.GetDefine(const AName: string): integer;
var
 idx:integer;
begin
   idx :=FDefineList.IndexOf(AName);
   if idx =-1 then
     // raise ECompException.CreateFmt('undeclared "%s"',[AName]);
     Result:=0
   else
     Result := Integer(FDefineList.Objects[idx]);
end;

procedure TPreProcessor.DelDefine(const AName: string);
var
 idx:integer;
begin
   idx :=FDefineList.IndexOf(AName);
   if idx =-1 then
      Exit;
   FDefineList.Objects[idx].Free();
   FDefineList.Delete(idx);
end;

procedure TPreProcessor.AddCurrenToken();
begin
   if CurrentToken = uuLine then
      Exit;
   if NewCount= Length(FTokensList)then
      SetLength(FTokensList,NewCount * 2);
   FTokensList[NewCount]:=Tokens[FPos-1];
   Inc(NewCount);
end;

function TPreProcessor.Parse(const ACode: string): integer;
begin
    inherited Parse(ACode);
    FTokensList:= nil;
    NewCount:= 0;
    FDefineList.Clear;
    SetLength(FTokensList,16);
    Section_Block(False,True);
    SetLength(FTokensList,NewCount);
    __Tokens:=FTokensList;
    SetLength(FTokensList,0);
    FLen     := NewCount;
    FPos     :=0;
    NewCount :=0;
    FDefineList.Clear;
    Result := Length(Tokens);
    fCurrentToken :=uuNone;
end;

procedure TPreProcessor.Section_Block(ASkip,AMove: boolean);
begin
    if AMove then
       NextToken();
    while CurrentToken<> uuNone do
    begin
      case CurrentToken of
               ppIf: ppIf_Stmt(ASkip);
            ppIfDef: ppIfDef_Stmt(ASkip);
           ppIfnDef: ppIfnDef_Stmt(ASkip);
             ppElIf: break;
             ppElse: break;
            ppEndIf: break;
      else if not ASkip then
           case CurrentToken of
               ppDefine: ppDefine_Stmt();
             ppUnDefine: ppUnDefine_Stmt();
              ppWarning: ppWrning_Stmt();
                ppError: ppError_Stmt();
           else
              AddCurrenToken();
           end;
      end;
      NextToken();
   end;
end;

function TPreProcessor.GetLineTxt: string;
var      
  Lt:integer;
begin
  Lt:=Tokens[FPos-1].mPos;
  while not (NextToken() in[uuLine,uuNone]) do
    ;
  with Tokens[FPos-1] do
      Result :=Result + Copy(FCode,Lt,mPos+mlen-Lt);
end;

procedure TPreProcessor.ppWrning_Stmt();
begin
   NextToken();
   Msg_Report(msWarning,GetLineTxt());
end;

procedure TPreProcessor.ppError_Stmt();
begin
   NextToken();
   Msg_Report(msError,GetLineTxt());
end;

procedure TPreProcessor.ppDefine_Stmt();
var
 U:integer;
 S:string;
begin
   NextToken();
   CheckCurrentToken(uuIdent);
   S:=GetTokenTxt();
   U:=ppPrimaryExpr(True,False);
   FDefineList.AddObject(S,Pointer(U));
   CheckCurrentToken(uuLine);
end;

function TPreProcessor.ppPrimaryExpr(AMove,ARequired: boolean): integer;
begin
    if AMove then
       NextToken();
    case CurrentToken of
            uuIdent: Result := GetDefine(GetTokenTxt());
        uuIntNumber: Result := StrToInt(GetTokenTxt());
        uuHexNumber: Result := StrToInt(GetTokenTxt());
            uuExprL: Result := ppParantExpr();
    else
      if ARequired then
         raise ECompException.Create('preprocessor expression expected');
      Result := 0;
      Exit;
    end;
    NextToken();
end;

function TPreProcessor.ppParantExpr: integer;
begin
    Result := ppBooleanExpr(True);
    CheckCurrentToken(uuExprR);
end;

function TPreProcessor.ppRelationalExpr(AMove: boolean): integer;
begin
   Result := ppPrimaryExpr(AMove,True);
    case CurrentToken of
           uuOpGr: Result:= integer(Result>ppPrimaryExpr(True,True));
         uuOpLess: Result:= integer(Result<ppPrimaryExpr(True,True));
        uuOpGrEqu: Result:= integer(Result<=ppPrimaryExpr(True,True));
      uuOpLessEqu: Result:= integer(Result>=ppPrimaryExpr(True,True));
    end;
end;

function TPreProcessor.ppEqualityExpr(AMove: boolean): integer;
begin
   Result := ppRelationalExpr(AMove);
    case CurrentToken of
         uuOpEqu: Result:= integer(Result=ppRelationalExpr(True));
      uuOpNotEqu: Result:= integer(Result<>ppRelationalExpr(True));
    end;
end;

function TPreProcessor.ppBooleanExpr(AMove: boolean): integer;
begin
   Result := ppEqualityExpr(AMove);
   while True do
    case CurrentToken of //boths Exprs Must be evalueted :to parse boths tokens
        uuOpCmpAnd:Result:= integer((Result<>0))and integer((ppEqualityExpr(True)<>0));
         uuOpCmpOr:Result:= integer((Result<>0))or integer((ppEqualityExpr(True)<>0));
       // uuOpCmpAnd:Result:= integer((Result<>0)and (ppEqualityExpr(True)<>0));
       //  uuOpCmpOr:Result:= integer((Result<>0)or(ppEqualityExpr(True)<>0));
    else
        break;
    end;
end;

procedure TPreProcessor.ppUnDefine_Stmt();
begin
   NextToken();
   CheckCurrentToken(uuIdent);
   DelDefine(GetTokenTxt());
   NextToken();
   CheckCurrentToken(uuLine);
end;

function TPreProcessor.ppCondition_Block(ASkip:boolean):boolean;
begin
   Result :=boolean(ppBooleanExpr(True));
   CheckCurrentToken(uuLine);
   Section_Block((not Result)or ASkip,True);
end;

procedure TPreProcessor.ppIf_Section(ATest,ASkip:boolean);
begin
   while CurrentToken = ppElIf do
   begin
       if ATest then
          Section_Block(True,True)
       else
          ATest := ppCondition_Block(ASkip);
   end;
   if CurrentToken = ppElse then
   begin
      NextToken();
      CheckCurrentToken(uuLine);
      Section_Block(ATest or ASkip,False);
   end;
   CheckCurrentToken(ppEndIf);
end;

procedure TPreProcessor.ppIf_Stmt(ASkip:boolean);
var
 Test:boolean;
begin
   Test:= ppCondition_Block(ASkip);
   ppIf_Section(Test , ASkip)
end;

procedure TPreProcessor.ppIfDef_Stmt(ASkip:boolean);
var
 Test:boolean;
begin
   NextToken();
   CheckCurrentToken(uuIdent);
   Test:= FDefineList.IndexOf(GetTokenTxt())<>-1;
   NextToken();
   CheckCurrentToken(uuLine);
   Section_Block((not Test)or ASkip,false);
   ppIf_Section(Test,ASkip);
end;

procedure TPreProcessor.ppIfnDef_Stmt(ASkip:boolean);
var
 Test:boolean;
begin
   NextToken();
   CheckCurrentToken(uuIdent);
   Test:= FDefineList.IndexOf(GetTokenTxt())<>-1;
   NextToken();
   CheckCurrentToken(uuLine);
   Section_Block( Test or ASkip,false);
   ppIf_Section(Test,ASkip);
end;

procedure TPreProcessor.Msg_Report(AMgsType:TMsgClass;ARes:PResStringRec);
begin
   Msg_Report(AMgsType,LoadResString(ARes));
end;

procedure TPreProcessor.Msg_Report(AMgsType: TMsgClass;const Arg: string;ALine:integer);
var
 Msg:TMsgRec;
begin
   Msg:=TMsgRec.Create;
   Msg.sMgsType :=AMgsType;
   Msg.sLine :=ALine;
   Msg.sArg  :=Arg;
   Msg.index :=__errindex;
   Msg.sData:=Data;
   FMsgsList.Add(Msg);
   inc(__errindex);
   if AMgsType in [msError] then
      inc(FErrorsCount);
end;

procedure TPreProcessor.Msg_Report(AMgsType: TMsgClass;const Arg: string);
begin
   Msg_Report(AMgsType,Arg,GetLine());
end;

function MsgSortFunc(AItem1,AItem2:Pointer):integer;
var
 A,B:TMsgRec;
begin
  A:=AItem1;
  B:=AItem2;
  if A.sLine > B.sLine then
     Result := 1
  else if A.sLine < B.sLine then
     Result := -1
  else if A.index > B.index then
     Result := 1
  else if A.index < B.index then
     Result := -1
  else
     Result := 0;
end;

procedure TPreProcessor.ExportMsgs(AList: TStrings);
const MSGS_CLASS:array [TMsgClass]of string =('','[Error]','[Warning]','[Note]');
var
 I:integer;
 S:string;
begin
   FMsgsList.Sort(MsgSortFunc);
   for I :=0 to FMsgsList.Count-1 do
   with FMsgsList.Items[I] do
    begin
      sLine := sLine and $FFFFFF;
      S:=MSGS_CLASS[sMgsType]+Name+'('+IntTostr(sLine+1)+'): '+sArg;
      AList.AddObject(S,FMsgsList.Items[I])
    end;
end;

{ TMsgsList }

function TMsgsList.GetItem(index: integer): TMsgRec;
begin
   Result := inherited Get(index)
end;

end.
