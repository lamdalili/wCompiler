unit USynParser;

interface
uses SysUtils,classes, ULexParser;
 type
   PintList=^TStaticarray;
   TStaticarray=array[0..0] of integer;
  TSynParser = class
  private
    FPosStack:PintList;
    FCount:integer;
    function GetTokensList: TPDataDynArray;
  protected
    FCode    :string;
    __Tokens  :TPDataDynArray;
    FPos     :integer;
    FLen     :integer;
    FCurrentToken :TokenType;
    procedure Err(ARes:PResStringRec);
    function Push():integer;
    function Pop(commit:boolean):integer;
    property Tokens:TPDataDynArray read GetTokensList;
  public
    destructor Destroy();override;
    function TryNextToken(Atok: TokenType): boolean;
    function TryCurrentToken(Atok: TokenType): boolean;
    function NextToken():TokenType;
    function Parse(const ACode:string):integer;virtual;
    function GetTokenTxt: string;
    function GetLine: integer;
    property CurrentToken: TokenType read FCurrentToken;
    function CheckCurrentAndMove(Atest: TokenType): TokenType;
    function CheckCurrentToken(Atest: TokenType): TokenType;
    function GetNextTokenAndCheck(Atest: TokenType): TokenType;
  end;

 function TokenName(tok:TokenType):string;
 function ExpectToken(tok:TokenType):string;
implementation
uses utils;
function TokenName(tok:TokenType):string;
begin
  case tok of
      uuBrassr:Result :='}';   uuBrassl:Result :='{';   uuOpor:Result :='|';
       uuOpand:Result :='&';   uuOpless:Result :='<';   uuOpgr:Result :='>';
    uuOpassign:Result :='=';   uuOpcomp:Result :='~';  uuOpnot:Result :='!';
      uuOptest:Result :='?';    uuOpxor:Result :='^'; uuOpdiv:Result :='/';
      uuOpstar:Result :='*';  uuOpmodul:Result :='%';    uuDef:Result :=':';
        uuIdxr:Result :=']';     uuIdxl:Result :='[';  uuExprr:Result :=')';
       uuExprl:Result :='(';  uuOpminus:Result :='-'; uuOpplus:Result :='+';
         uuSep:Result :=',';  uuInstsep:Result :=';';  uuOpdot:Result :='.';
      uuMinusAssign :Result :='-=';  uuPlusAssign:Result :='+=';
       uuOpcmpor:Result :='||';   uuOpcmpand:Result :='&&';
         uuOpshr:Result :='>>';    uuOpshl:Result :='<<';      uuOpdec:Result :='--';
         uuOpinc:Result :='++'; uuOpnotequ:Result :='!=';      uuOpequ:Result :='==';
     uuOplessequ:Result :='<=';  uuOpgrequ:Result :='>=';

     uuIntnumber:Result :='Int number';  uuVar:Result :='Var';
     uuCharacter:Result :='Character';  uuLine:Result :='Line';
     uuHexnumber:Result :='Hex number';uuIdent:Result :='Identifier';
   uuFloatnumber:Result :='Float number'; uuIf:Result :='If';
      uuReadonly:Result :='Readonly'; uuUshort:Result :='UShort';
          uuType:Result :='Type';     uuSizeof:Result :='Sizeof';
          uuFunc:Result :='Func';      uuConst:Result :='Const';
        uuStatic:Result :='Static';   uuReturn:Result :='Return';
       uuDefault:Result :='Default';    uuCase:Result :='Case';
       uuSwitch :Result :='Switch'; uuContinue:Result :='Continue';
         uuBreak:Result :='Break';       uuFor:Result :='For';
          uuElse:Result :='Else';         uuDo:Result :='Do';
         uuWhile:Result :='While';      uuText:Result :='Text';
          uuEnum:Result :='Enum';      uuUnion:Result :='Union';
        uuStruct:Result :='Struct';    uuUsing:Result :='Using';
         uuFloat:Result :='Float';      uuTrue:Result :='True';
         uuFalse:Result :='False';      uuNull:Result :='Null';
          uuGoto:Result :='Goto';      uuShort:Result :='Short';
         uuSbyte:Result :='SByte';      uuByte:Result :='Byte';
          uuVoid:Result :='Void';       uuUint:Result :='UInt';
          uuChar:Result :='Char';       uuBool:Result :='Bool';
           uuInt:Result :='Int';
           uuImplementation:Result :='Implementation';
      uuAbstract:Result :='Abstract';uuVirtual:Result :='Virtual';
          uuBase:Result :='Base';   uuNew:Result :='New';
      uuOverride:Result :='Override';  uuClass:Result :='Class';
        uuPublic:Result :='Public';  uuPrivate:Result :='Private';
     uuProtected:Result :='Protected'; uuLocal:Result :='Local';
     uuInterface:Result :='Interface'; uuEvent:Result :='Event';
          uuBind:Result :='Bind';        uuRef:Result :='Ref';
            uuIs:Result :='Is';           uuAs:Result :='As';
           uuTry:Result :='Try';     uuFinally:Result :='Finally';
         uuCatch:Result :='Catch';     uuThrow:Result :='Throw';
  else
     Result :='parser error';
  end;
end;

function ExpectToken(tok:TokenType):string;
begin
    Result := ''''+TokenName(tok)+''' expected';
end;

{ TYCompiler }

procedure TSynParser.Err(ARes:PResStringRec);
begin
    raise ECompException.CreateRes(ARes);
end;

function TSynParser.GetNextTokenAndCheck(Atest:TokenType):TokenType;
begin
  Result :=NextToken;
  if Result<> Atest then
     raise ECompException.Create(ExpectToken(Atest));
end;

function TSynParser.CheckCurrentToken(Atest:TokenType):TokenType;
begin
  Result :=CurrentToken;
  if Result<> Atest then
     raise ECompException.Create(ExpectToken(Atest));
end;

function TSynParser.CheckCurrentAndMove(Atest:TokenType):TokenType;
begin
  if CurrentToken<> Atest then
     raise ECompException.Create(ExpectToken(Atest));
   Result :=NextToken;
end;

destructor TSynParser.Destroy;
begin
  Reallocmem(FPosStack,0);
  inherited;
end;

function TSynParser.Push():integer;
begin
     Result := FCount;
     Reallocmem(FPosStack,(Result+1)*SizeOf(Integer));
     FPosStack[Result]:=FPos;
     inc(FCount);
end;

function TSynParser.Pop(commit:boolean):integer;
begin
     Result := FCount-1;
     if not commit then
       FPos := FPosStack[Result];
     FCurrentToken :=Tokens[FPos-1].mToken ;
     Reallocmem(FPosStack, Result *SizeOf(Integer));
     dec(FCount);
end;

function TSynParser.NextToken(): TokenType;
begin
    if FPos >= FLen then
    begin
      Result :=uuNone ;
      FCurrentToken :=uuNone ;
      Exit;
    end;
    Result :=Tokens[FPos].mToken;
    FCurrentToken := Result;
    Inc(FPos);
end;

function TSynParser.TryNextToken(Atok:TokenType):boolean;
var
 t:TokenType;
begin
    if FPos >= FLen then
    begin
      Result :=False;
      Exit;
    end;
    t:=Tokens[FPos].mToken;
    Result :=Atok=t;
    if Result then
    begin
      FCurrentToken := t;
      Inc(FPos);
    end;
end;

function TSynParser.TryCurrentToken(Atok:TokenType):boolean;
begin
    if FPos >= FLen then
    begin
      Result :=False;
      Exit;
    end;
    Result :=Atok=FCurrentToken;
    if Result then
    begin
      FCurrentToken := Tokens[FPos].mToken;
      Inc(FPos);
    end;
end;

function TSynParser.Parse(const ACode: string): integer;
begin
    FCode := ACode;
    BuildTokens(FCode,__Tokens);
    Result := Length(Tokens);
    FLen := Result;
    FPos     :=0;
    FPosStack:=nil;
end;

function TSynParser.GetTokenTxt: string;
begin
   with Tokens[FPos-1] do
     Result:= Copy(FCode,mPos,mLen);
end;

function TSynParser.GetLine: integer;
begin
    Result:= Tokens[FPos-1].mLine;
end;

function TSynParser.GetTokensList: TPDataDynArray;
begin
   if __Tokens=nil then
     raise ECompException.Create('empty code source');
   Result :=__Tokens;
end;

initialization
  DecimalSeparator:='.';
end.
