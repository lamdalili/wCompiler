unit Utils;

interface
uses
  SysUtils, Classes;
type
  ECompException=class(Exception);
  TQSList = class
  protected
    FData: PPointerList;
    FCapacity: integer;
    FCount: integer;
    procedure Grow;
    procedure SetCapacity(NewCapacity: Integer);
    procedure SetCount(const Value: integer);
    procedure CheckIndex(Aidx: integer);
  public
    function Peek: Pointer;
    function Pop: Pointer;
    function IndexOf(obj:Pointer):integer;
    procedure Delete(Aidx: integer); virtual;
    procedure SetItem(Aidx: integer; AValue: Pointer);
    function GetItem(Aidx: integer): Pointer;
    destructor Destroy; override;
    property Count: integer read FCount write SetCount;
    function Add(P: Pointer): integer;
    function Push(P: Pointer): Pointer;
    procedure Clear; virtual;
    property Items[index:integer]:Pointer read GetItem write SetItem; default;
  end;

  TQSObjList = class(TQSList)
  protected
    FOwnObjs: boolean;
    function GetItem(index: integer): TObject;
    procedure SetItem(index: integer; const Value: TObject);
  public
    function Add(Obj: TObject): integer;
    procedure Clear; override;
    procedure Delete(Aidx: integer); override;
    property Objs[index:integer]:TObject read GetItem write SetItem; default;
    property OwnObjs:boolean read FOwnObjs write FOwnObjs;
  end;
  function BoolToStr(Value:boolean):string;
implementation


{ TQSList }

function TQSList.Add(P: Pointer): integer;
begin
    Result :=FCount;
    if Result = FCapacity then
       Grow();
    FData[Result]:= P;
    inc(FCount);
end;

procedure TQSList.Clear;
begin
    Reallocmem(FData,0);
    FCount := 0;
    FCapacity :=0;
    FData := nil;
end;

destructor TQSList.Destroy;
begin
  Clear();
  inherited;
end;

procedure TQSList.SetCapacity(NewCapacity: Integer);
begin
    FCapacity := NewCapacity;
    Reallocmem(FData,FCapacity * SizeOf(Pointer));
end;

procedure TQSList.Grow;
var
  Delta: Integer;
begin
  if FCapacity > 64 then
    Delta := FCapacity div 4
  else
    if FCapacity > 8 then
      Delta := 16
    else
      Delta := 4;
  SetCapacity(FCapacity + Delta);
end;

procedure TQSList.SetCount(const Value: integer);
begin
  if FCapacity < Value then
     SetCapacity(Value);
  FillChar(FData^[FCount], (Value - FCount) * SizeOf(Pointer), 0);
  FCount := Value;
end;

procedure TQSList.CheckIndex(Aidx: integer);
begin
  if (Aidx < 0) or (Aidx >= FCount) then
     raise ECompException.Create('index out of Qslist');
end;

function TQSList.GetItem(Aidx: integer): Pointer;
begin
   CheckIndex(AIdx);
   Result := FData[AIdx];
end;

procedure TQSList.SetItem(Aidx: integer;AValue:Pointer);
begin
   CheckIndex(AIdx);
   FData[AIdx] := AValue;
end;

procedure TQSList.Delete(Aidx: integer);
begin
  CheckIndex(AIdx);
  Dec(FCount);
  if Aidx < FCount then
    System.Move(FData^[AIdx + 1], FData^[AIdx],
      (FCount - AIdx) * SizeOf(Pointer));
end;

function TQSList.Peek():Pointer;
begin
  CheckIndex(FCount-1);
  Result := FData[FCount-1];
end;

function TQSList.Pop():Pointer;
begin
  Result := Peek();
  Dec(FCount);
end;

function BoolToStr(Value:boolean):string;
begin
  if Value then
    Result :='True'
  else
    Result :='False'
end;

function TQSList.Push(P: Pointer): Pointer;
begin
    if Count <>0 then
       Result := Items[Count-1]
    else
       Result :=nil;
    Add(P);
end;

function TQSList.IndexOf(obj: Pointer): integer;
begin
   for Result :=0 to Count -1 do
      if Items[Result]=obj then
         Exit;
   Result :=-1;
end;

{ TQSObjList }

function TQSObjList.Add(Obj: TObject): integer;
begin
     Result :=inherited Add(Obj);
end;

procedure TQSObjList.Clear;
var
  I:integer;
begin
  if FOwnObjs then
   for I :=Count -1 downto 0 do
      Objs[I].Free;

  inherited;
end;

procedure TQSObjList.Delete(Aidx: integer);
begin
  if FOwnObjs then
     Objs[Aidx].Free;
  inherited;
end;

function TQSObjList.GetItem(index: integer): TObject;
begin
    Result := Items[index];
end;

procedure TQSObjList.SetItem(index: integer; const Value: TObject);
begin
    Items[index] :=Value;
end;



end.
