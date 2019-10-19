unit UCommon;

interface
uses
    SysUtils,Classes,Utils;
type
  TResBucket =class
  private
    FData:PByteArray;
    FSize:integer; 
    procedure SetCount(const Value: integer);
  public
    destructor Destroy; override;
    property Data:PByteArray read FData;
    property Size:integer read FSize write SetCount;
    function Append(const Src; Count: integer):TResBucket;
    function AppendStr(const Src; Count,StrLen: integer):TResBucket;
    function Clone():TResBucket;
  end;
  TListKind=(ssConstsList,ssNamesList,ssAlloc,ssActiveCodeStmt,ssActiveErrSync,
             ssObjectList,ssFuncList,ssFinallySection);
  TListKindSet =set of TListKind;
  TStacks =class
  private
    FList:TQSList;
    FPopList:TQSList;
    function GetList(AIdx: TListKind):TObject;
    function GetLevel: integer;
  public  
    constructor Create;
    destructor Destroy; override;
    procedure Push(AObj:TObject;ALists:TListKindSet);
    procedure Pop();
    property Lists[AIdx:TListKind]:TObject read GetList;default;
    property Level:integer read GetLevel;
  end;
  const
    STRUCT_LISTS:TListKindSet=[ssNamesList,ssConstsList,ssAlloc,ssObjectList,ssFuncList];
implementation

{ TStacks }

constructor TStacks.Create;
var
 U:TListKind;
begin
   FList:=TQSList.Create;
   FPopList :=TQSList.Create;
   for U := Low (TListKind)to high(TListKind) do
    FList.Add(TQSObjList.Create);
   Push(nil,[Low(TListKind)..high(TListKind)]);
end;
type
   PListKindSet=^TListKindSet;
destructor TStacks.Destroy;

var
 U:TListKind;
 I:integer;
begin
  Pop();
  for U := Low (TListKind)to high(TListKind) do
    TQSList(FList[Ord(U)]).Free;
  for I := 0 to FPopList.Count-1 do
    Dispose(PListKindSet(FPopList[I]));

  FPopList.Free;
  FList.Free;
  inherited;
end;

function TStacks.GetLevel: integer;
begin
    Result:= FPopList.Count;
end;

function TStacks.GetList(AIdx: TListKind): TObject;
begin
     Result :=TObject( TQSList(FList[Ord(AIdx)]).Peek);
end;

procedure TStacks.Pop();
var
 U:TListKind;
 P:PListKindSet;
begin
   P:=FPopList.Pop;
   for U := Low (TListKind)to high(TListKind) do
     if U in P^ then
       TQSList(FList[Ord(U)]).Pop();

end;

procedure TStacks.Push(AObj: TObject; ALists: TListKindSet);
var
 U:TListKind;
 P:PListKindSet;
begin
   New(P);
   P^:=ALists;
   FPopList.Add(P);
   for U := Low (TListKind)to high(TListKind) do
     if U in ALists then
        TQSList(FList[Ord(U)]).Add(AObj);
end;

{ TResCel }

function TResBucket.Append(const Src; Count: integer):TResBucket;
var
 OldSize:integer;
begin
   OldSize :=FSize;
   Size := OldSize + Count;
   Move(Src,FData[OldSize],Count);
   Result :=Self;
end;

function TResBucket.AppendStr(const Src; Count,StrLen: integer): TResBucket;
var
 OldSize:integer;
 ToCopy:integer;
begin
   ToCopy := Count;
   if StrLen < Count then
      ToCopy := StrLen;
   OldSize :=FSize;
   Size := OldSize + Count;
   Move(Src,FData[OldSize],ToCopy);
   Result :=Self;
end;

function TResBucket.Clone: TResBucket;
begin
   Result := TResBucket.Create;
   Result.SetCount(Size);
   Move(FData^,Result.FData^,FSize);
end;

destructor TResBucket.Destroy;
begin
  ReallocMem(FData,0);
  inherited;
end;

procedure TResBucket.SetCount(const Value: integer);
var
 zPos:integer;
begin
  zPos :=FSize;
  ReallocMem(FData,Value);
  FSize := Value;
  if FSize <> 0 then
     FillChar(FData^[zPos],FSize-zPos,0);
end;

end.
