unit UStaticHashTable;
interface
type
  TKey   = string;
  TValue = integer;
  TItem = record
    HashCode: Cardinal;
    Key: TKey;
    Value: TValue;
  end;

  TStaticHashTable = class
  private
    FItems: array of TItem;
    FCount: Integer;
    FMaxLen :Integer;
    FHash   :Cardinal;
    FIndex  :integer;
    function Find(const AKey: TKey): boolean;
    function HashOf(const AKey: TKey): Cardinal;
  public
    constructor Create(ACapacity: Integer);overload;
    constructor Create(const AItems: array of string);overload;
    procedure Add(const AKey: TKey; const AValue: TValue);
    function ValueOf(const Key: TKey): TValue;
  end;

implementation
uses SysUtils;

const INVALIDVALUE:TValue=-1;

constructor TStaticHashTable.Create(ACapacity: Integer );
var
  Cap: Integer;
begin
    Cap := 4;
    ACapacity:= ACapacity + (ACapacity shr 1);
    while Cap < ACapacity do
      Cap := Cap shl 1;
    SetLength(FItems,Cap);
    FMaxLen:= Cap * 4 div 3;
end;

constructor TStaticHashTable.Create(const AItems: array of string);
var
 I:integer;
begin
     Create(Length(AItems));
     for I := 0 to Length(AItems)-1 do
         Add(AItems[I],I);
end;

function TStaticHashTable.Find(const AKey: TKey): boolean;
begin
    FHash:=HashOf(AKey);
    FIndex:= FHash and $7FFFFFFF;
    Result := True;
    repeat
      FIndex:= FIndex and (Length(FItems)-1) ;
      with FItems[FIndex] do
      begin
          if HashCode = 0 then
            break
          else if (HashCode = FHash)and (Key = AKey)then
            Exit
          else
            inc(FIndex);
      end;
    until False;
    Result := False;
end;

function TStaticHashTable.HashOf(const AKey: TKey): Cardinal;
var I:integer;
begin
  Result :=  0;
  for I := 1 to Length(AKey) do
    Result := (Result shl 3) xor Result xor Ord(AKey[I]);
end;

procedure TStaticHashTable.Add(const AKey: TKey; const AValue: TValue);
begin
  if Find(AKey) then Exit;
  if FCount+1 > FMaxLen then
     raise Exception.Create('Capacity overflow');
  with FItems[FIndex] do begin
     HashCode := FHash;
     Key      := AKey;
     Value    := AValue;
  end;
  inc(FCount);
end;

function TStaticHashTable.ValueOf(const Key: TKey):TValue;
begin
   if Find(Key)then
      Result := FItems[FIndex].Value
   else
      Result := INVALIDVALUE
end;


end.

