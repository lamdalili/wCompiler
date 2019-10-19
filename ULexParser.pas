unit ULexParser;

interface
{ *********************************************************************** }
{                                                                         }
{ Delphi Lex  generator                                                   }
{                                                                         }
{ Copyright (c) Sweet Lex  by Montor                                      }
{ Released:   27/01/2015 13:55:17                                         }
{ *********************************************************************** }


uses SysUtils,UStaticHashTable;
 type
  TokenType = (uuNone ,uuInvalid, uuOptest, uuBrassr, uuBrassl, uuOpor,
 uuOpand, uuOpxor, uuOpmodul, uuIdxr, uuIdxl, uuExprr, uuExprl, uuSep,
 uuOpless, uuOpgr, uuOpassign, uuOpcomp, uuOpnot,uuOpdiv,  uuOpstar,
 uuOpminus, uuOpplus, uuDef, uuInstsep, uuOpdot,uuMemberPtr, uuPreprocessor, uuText,
 uuCharacter, uuCommen, uuComment, uuIdent, uuFloatnumber, uuHexnumber,
 uuLine, uuWhite, uuIntnumber,uuMinusAssign,uuPlusAssign,
 uuOpcmpor, uuOpcmpand, uuOpshr, uuOpshl, uuOpdec, uuOpinc,
 uuOpgrequ, uuOplessequ, uuOpnotequ, uuOpequ, ppwarning, pperror,
 ppifndef, ppifdef, ppinclude, ppundefine, ppdefine, ppelif,
 ppendif, ppelse, ppif, uuAsm,
 uuEvent,uuSizeof, uuReadonly,uuUshort, uuShort, uuSbyte,
 uuByte, uuVoid, uuChar, uuUint,uuInt, uuBool, uuType, uuVar, uuFunc,
 uuConst, uuStatic, uuReturn, uuDefault, uuCase, uuSwitch,
 uuContinue, uuBreak, uuFor, uuElse,uuDo, uuWhile, uuIf, uuEnum, uuUnion,
 uuStruct, uuUsing,uuFloat,uuTrue,uuFalse,uuNull,uuGoto,
 uuImplementation,uuLink,uuPrint,uuInline,
 uuPublic,uuPrivate,uuProtected,uuLocal,
 uuClass,uuAbstract, uuOverride, uuVirtual,uuBase,uuNew,
 uuInterface,uuBind,uuIs,uuAs,uuRef,uuTry,uuFinally,uuCatch,uuThrow);

  TYProc = function :boolean of object;
  TTokenSet =set of TokenType;
  TByteSet = set of byte;
  TLexCompiler= class
  private

 // protected
    FCode :string;
    FPos  :integer;
    FChar :integer;
    FCopy :integer;
    FTokenList :TStaticHashTable;
    FReturn:TokenType;
    function ProcMemberPtr: boolean;
    function TrySet(const ASet:TByteSet):boolean;
    function TryNext(const ATok:integer):boolean;
    function Gets():integer;
    procedure SetCode(const Value: string);
    function RepReq(const C: TYProc; ARetType: TokenType =uuNone): boolean;
    function RepOp(const C: TYProc): boolean;
    function Op(const C: TYProc): boolean;
    function Req(const C: TYProc; ARetType: TokenType =uuNone): boolean;
    procedure LHashTest;
    function ProcOpEqu:boolean;
    function ProcOpNotEqu:boolean;
    function ProcOpLessEqu:boolean;
    function ProcOpGrEqu:boolean;
    function ProcOpInc:boolean;
    function ProcOpDec:boolean;
    function ProcOpShl:boolean;
    function ProcOpShr:boolean;
    function ProcOpCmpAnd:boolean;
    function ProcOpCmpOr:boolean;
    function ProcOpPlusAssign:boolean;
    function ProcOpMinusAssign:boolean;
    function ProcIntNumber:boolean;
    function Procwhite:boolean;
    function Proc_line_01:boolean;
    function Procline:boolean;
    function Proc_HexNumber_01:boolean;
    function ProcHexNumber:boolean;
    function Proc_exp_01:boolean;
    function Procexp:boolean;
    function Proc_FloatNumber_01:boolean;
    function Proc_FloatNumber_02:boolean;
    function Proc_FloatNumber_03:boolean;
    function ProcFloatNumber:boolean;
    function Proc_Ident_01:boolean;
    function ProcIdent:boolean;
    function Proc_comment_01:boolean;
    function Proccomment:boolean;
    function Proc_commen_01:boolean;
    function Proc_commen_02:boolean;
    function Proccommen:boolean;
    function Proccharacter:boolean;
    function Proc_text_01:boolean;
    function Proctext:boolean;
    function Proc_PreProcessor_01:boolean;
    function ProcPreProcessor:boolean;
    function CharsList:boolean;
    function Proc_char_01: boolean;
  public
    constructor Create();
    destructor Destroy();override;
    function NextToken():TokenType;
    function TokenTxt():string;
    property Code:string read FCode write SetCode;
    property CurrToken:TokenType read FReturn;
  end;

 ELexError = class(Exception);
  TPData =record
      mToken :TokenType;
      mPos :integer;
      mLen :integer;
      mLine:integer;
  end;
  TPDataDynArray = array of TPData;
  procedure BuildTokens(const ACode: string;var AStack:TPDataDynArray);
  const
   ELEX_EOF = 10;
   SKIP_TOKENS: set of TokenType = [uuCommen, uuComment, uuWhite];
implementation

function LinesCount(const ACode: string):integer;
var
  I:integer;
begin
   I:= 1;
   Result :=0;
   while I<=Length(ACode)do
   begin
      if (ACode[I]=#13)and(ACode[I+1]=#10) then
      begin
         Result :=Result +1;
         inc(I);
      end;
      inc(I);
   end;
end;

procedure BuildTokens(const ACode: string;var AStack:TPDataDynArray);
var
  Tmp:TPData;
  Len:Integer;
  Line :Integer;
begin
  Len := 0;
  Line :=0;
  SetLength(AStack,4);
  with TLexCompiler.Create,Tmp do
    try
          Code := ACode;
          repeat
                if Len = Length(AStack)then
                   SetLength(AStack,Len * 2);
                while  NextToken in SKIP_TOKENS do
                  begin
                     Line := Line + LinesCount(TokenTxt())
                  end;
                mLine := Line;
                if CurrToken=uuLine then
                   inc(Line);
                mToken:= FReturn;
                mPos  := FCopy + 1;
                mLen  := FPos - FCopy;
                AStack[Len] :=Tmp;
                inc(Len);
          until Ord(mToken) = 0;
    finally
        Free();
    end;
  SetLength(AStack,Len);
end;
{ TLexCompiler }

constructor TLexCompiler.Create;
begin
   FTokenList :=TStaticHashTable.Create(['#WARNING', '#ERROR',
 '#IFNDEF', '#IFDEF', '#INCLUDE', '#UNDEFINE', '#DEFINE', '#ELIF',
 '#ENDIF', '#ELSE', '#IF','ASM',
 'EVENT','SIZEOF', 'FIX','USHORT', 'SHORT', 'SBYTE', 'BYTE', 'VOID', 'CHAR', 'UINT',
 'INT', 'BOOL', 'TYPE', 'VAR', 'FUNC', 'CONST', 'STATIC',
 'RETURN', 'DEFAULT', 'CASE', 'SWITCH', 'CONTINUE', 'BREAK', 'FOR', 'ELSE',
 'DO', 'WHILE', 'IF', 'ENUM', 'UNION', 'STRUCT', 'USING',
 'FLOAT','TRUE','FALSE','NULL','GOTO','IMP','LINK','PRINT','INLINE',
 'PUBLIC','PRIVATE','PROTECTED','LOCAL',
 'CLASS','ABSTRACT','OVERRIDE','VIRTUAL','BASE','NEW',
 'INTERFACE','BIND','IS','AS','REF','TRY','FINALLY','CATCH','THROW']);
end;

destructor TLexCompiler.Destroy;
begin
  FTokenList.Free;
  inherited;
end;

function TLexCompiler.Gets: integer;
begin
    if FPos  > Length(FCode) then
       raise ELexError.Createhelp('eof err',ELEX_EOF);
    Inc(FPos);
    FChar:=Ord(FCode[FPos]);
    Result:= FChar;
end;

function TLexCompiler.TrySet(const ASet: TByteSet): boolean;
begin
        Result:= Gets in ASet;
        if not Result then
           dec(FPos);
end;

function TLexCompiler.TryNext(const ATok: integer): boolean;
begin
        Result:= Gets = ATok;
        if not Result then
           dec(FPos);
end;

procedure TLexCompiler.SetCode(const Value: string);
begin
  FCode := Value;
  FPos  := 0;
  FCopy := 0;
end;

function TLexCompiler.RepReq(const C:TYProc;ARetType:TokenType):boolean;
var
  OldPos,MuchCount :integer;
begin
  MuchCount:= 0;
  repeat
    OldPos := FPos;
    Result := C;
    if not Result then FPos := OldPos;
    inc(MuchCount);
  until Result = False;
  Result := MuchCount > 1;
  if Result and (ARetType <> uuNone)then
      FReturn := ARetType;
end;

function TLexCompiler.RepOp(const C:TYProc):boolean;
var
  OldPos :integer;
begin
  repeat
    OldPos := FPos;
    Result := C;
    if not Result then FPos := OldPos;
  until Result = False;
  Result := True;
end;

function TLexCompiler.Op(const C:TYProc):boolean;
var
  OldPos :integer;
begin
    OldPos := FPos;
    Result := C;
    if not Result then FPos := OldPos;
    Result := True;
end;

function TLexCompiler.Req(const C:TYProc;ARetType:TokenType):boolean;
var
  OldPos :integer;
begin
    OldPos := FPos;
    Result := C;
    if not Result then FPos := OldPos;
    if Result and (ARetType <> uuNone)then
       FReturn := ARetType;
end;

procedure TLexCompiler.LHashTest();
var
 V:integer;
begin
    V:= FTokenList.ValueOf(UpperCase(TokenTxt));
    if V <> -1 then
       FReturn := TokenType(Ord(ppwarning)+V);
end;

function TLexCompiler.TokenTxt: string;
begin
    Result := Copy(FCode,FCopy+1,FPos-FCopy);
end;

function TLexCompiler.ProcOpEqu:boolean;
begin
  Result := (Gets = 61) and (Gets = 61);
end;

function TLexCompiler.ProcOpNotEqu:boolean;
begin
  Result := (Gets = 33) and (Gets = 61);
end;

function TLexCompiler.ProcOpLessEqu:boolean;
begin
  Result := (Gets = 60) and (Gets = 61);
end;

function TLexCompiler.ProcOpGrEqu:boolean;
begin
  Result := (Gets = 62) and (Gets = 61);
end;

function TLexCompiler.ProcOpInc:boolean;
begin
  Result := (Gets = 43) and (Gets = 43);
end;

function TLexCompiler.ProcOpDec:boolean;
begin
  Result := (Gets = 45) and (Gets = 45);
end;

function TLexCompiler.ProcOpShl:boolean;
begin
  Result := (Gets = 60) and (Gets = 60);
end;

function TLexCompiler.ProcOpShr:boolean;
begin
  Result := (Gets = 62) and (Gets = 62);
end;

function TLexCompiler.ProcOpCmpAnd:boolean;
begin
  Result := (Gets = 38) and (Gets = 38);
end;

function TLexCompiler.ProcMemberPtr:boolean;
begin
  Result := (Gets = 45) and (Gets = 62);
end;

function TLexCompiler.ProcOpCmpOr:boolean;
begin
  Result := (Gets = 124) and (Gets = 124);
end;

function TLexCompiler.ProcOpPlusAssign:boolean;
begin
  Result := (Gets = 43) and (Gets = 61);
end;

function TLexCompiler.ProcOpMinusAssign:boolean;
begin
  Result := (Gets = 45) and (Gets = 61);
end;

function TLexCompiler.ProcIntNumber:boolean;
begin
  Result := (Gets in [48..57]);
end;

function TLexCompiler.Procwhite:boolean;
begin
  Result := TrySet([1..9]) or TrySet([11..12])
                   or TrySet([14..32]);
end;

function TLexCompiler.Proc_line_01:boolean;
begin
  Result := (Gets = 13) and (Gets = 10);
end;

function TLexCompiler.Procline:boolean;
begin
  Result :=  Req(Proc_line_01) or TryNext(10)
                   or TryNext(13);
end;

function TLexCompiler.Proc_HexNumber_01:boolean;
begin
  Result := (Gets in [48..57,97..102,65..70]);
end;

function TLexCompiler.ProcHexNumber:boolean;
begin
  Result := (Gets = 48) and (Gets in [120,88])
                   and  RepReq(Proc_HexNumber_01);
end;

function TLexCompiler.Proc_exp_01:boolean;
begin
  Result := (Gets in [43,45]);
end;

function TLexCompiler.Procexp:boolean;
begin
  Result := (Gets in [69,101]) and  Op(Proc_exp_01)
                   and  RepReq(ProcintNumber,uuIntnumber);
end;

function TLexCompiler.Proc_FloatNumber_01:boolean;
begin
  Result :=  RepReq(ProcintNumber,uuIntnumber);
end;

function TLexCompiler.Proc_FloatNumber_02:boolean;
begin
  Result := (Gets = 46) and  Op(Proc_FloatNumber_01);
end;

function TLexCompiler.Proc_FloatNumber_03:boolean;
begin
  Result :=  Req(Procexp);
end;

function TLexCompiler.ProcFloatNumber:boolean;
begin
  Result :=  RepReq(ProcintNumber,uuIntnumber) and  Req(Proc_FloatNumber_02)
                   and  Op(Proc_FloatNumber_03);
end;

function TLexCompiler.Proc_Ident_01:boolean;
begin
  Result := (Gets in [97..122,65..90,95,48..57]);
end;

function TLexCompiler.ProcIdent:boolean;
begin
  Result := (Gets in [97..122,65..90,95]) and  RepOp(Proc_Ident_01);
end;

function TLexCompiler.Proc_comment_01:boolean;
begin
  Result :=  not ((Gets in [0,10,13]));
end;

function TLexCompiler.Proccomment:boolean;
begin
  Result := (Gets = 47) and (Gets = 47)
                   and  RepOp(Proc_comment_01);
end;

function TLexCompiler.Proc_commen_01:boolean;
begin
  Result :=  not ((Gets = 42) and (Gets = 47));
end;

function TLexCompiler.Proc_commen_02:boolean;
begin
  Result :=  Req(Proc_commen_01);
end;

function TLexCompiler.Proccommen:boolean;
begin
  Result := (Gets = 47) and (Gets = 42)
                   and  RepOp(Proc_commen_02)
                     and (Gets = 42)
                       and (Gets = 47);
end;

function TLexCompiler.Proc_char_01:boolean;
begin
  Result :=  not ((Gets in [0,10,13,39]));
  // (Gets in [0..255])
end;

function TLexCompiler.Proccharacter:boolean;
begin
  Result := (Gets = 39) and RepOp(Proc_char_01)
                   and (Gets = 39);
end;

function TLexCompiler.Proc_text_01:boolean;
begin
  Result :=  not ((Gets in [0,10,13,34]));
end;

function TLexCompiler.Proctext:boolean;
begin
  Result := (Gets = 34) and  RepOp(Proc_text_01)
                   and (Gets = 34);
end;

function TLexCompiler.Proc_PreProcessor_01:boolean;
begin
  Result := (Gets in [97..122,65..90,95,48..57]);
end;

function TLexCompiler.ProcPreProcessor:boolean;
begin
  Result := (Gets = 35) and (Gets in [97..122,65..90,95])
                   and  RepOp(Proc_PreProcessor_01);
end;

function TLexCompiler.CharsList:boolean;
begin
   Result := True;
   case Gets of
     63: FReturn := uuOptest;
     125: FReturn := uuBrassr;
     123: FReturn := uuBrassl;
     124: FReturn := uuOpor;
     38: FReturn := uuOpand;
     94: FReturn := uuOpxor;
     37: FReturn := uuOpmodul;
     93: FReturn := uuIdxr;
     91: FReturn := uuIdxl;
     41: FReturn := uuExprr;
     40: FReturn := uuExprl;
     44: FReturn := uuSep;
     60: FReturn := uuOpless;
     62: FReturn := uuOpgr;
     61: FReturn := uuOpassign;
     126: FReturn := uuOpcomp;
     33: FReturn := uuOpnot;
     47: FReturn := uuOpdiv;
     42: FReturn := uuOpstar;
     45: FReturn := uuOpminus;
     43: FReturn := uuOpplus;
     58: FReturn := uuDef;
     59: FReturn := uuInstsep;
     46: FReturn := uuOpdot;
   else 
     Result := False;
   end;
   if not Result then
     Dec(FPos);
end;

function TLexCompiler.NextToken:TokenType;
begin
  if FPos >= Length(FCode)then
  begin 
     Result  := uuNone;
     FReturn := uuNone;
     FCopy   := FPos;
     Exit;
  end;
  FCopy := FPos;
  if not( Req(ProcPreProcessor,uuPreprocessor)
                 or  Req(Proctext,uuText)
                  or  Req(Proccharacter,uuCharacter)
                   or  Req(Proccommen,uuCommen)
                    or  Req(Proccomment,uuComment)
                     or  Req(ProcIdent,uuIdent)
                      or  Req(ProcFloatNumber,uuFloatnumber)
                       or  Req(ProcHexNumber,uuHexnumber)
                        or  Req(Procline,uuLine)
                         or  RepReq(Procwhite,uuWhite)
                          or  RepReq(ProcIntNumber,uuIntnumber)
                           or  Req(ProcOpMinusAssign,uuMinusAssign)
                            or  Req(ProcOpPlusAssign,uuPlusAssign)
                             or  Req(ProcMemberPtr,uuMemberPtr)
                              or  Req(ProcOpCmpOr,uuOpcmpor)
                               or  Req(ProcOpCmpAnd,uuOpcmpand)
                                or  Req(ProcOpShr,uuOpshr)
                                 or  Req(ProcOpShl,uuOpshl)
                                  or  Req(ProcOpDec,uuOpdec)
                                   or  Req(ProcOpInc,uuOpinc)
                                    or  Req(ProcOpGrEqu,uuOpgrequ)
                                     or  Req(ProcOpLessEqu,uuOplessequ)
                                      or  Req(ProcOpNotEqu,uuOpnotequ)
                                       or  Req(ProcOpEqu,uuOpequ)
                                        or CharsList) then begin
     FReturn := uuInvalid;
     inc(FPos);
  end; 
  if FReturn in [uuPreprocessor, uuIdent] then
     LHashTest();
  Result :=  FReturn;
end;

end.



