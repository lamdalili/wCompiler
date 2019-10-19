unit USymbolesTable;

interface
uses
    SysUtils,Classes,UNodesBase,Utils,UTypes,UCommon,Dialogs;

type
  TSymIdent =class;
  TSymBaseClass = class of TSymIdent;
  TScope  = class;
  TScopeBaseClass  =  class of TScope;
  TBaseUnit  = class;

  TSymSearchList = class
  protected
    FMutch:TSymIdent;
    FText:string;
    FHash:integer;
    procedure SetText(const Value: string);
  public
    procedure Clear();
    procedure Add(Sym:TSymIdent);
    property Mutch:TSymIdent read FMutch;
    property Text:string read FText write SetText;
  end;

  PSymIdent=  ^TSymIdent;
  TSymIdent = class(TSymbolExpr)
  private
    _HashCode:integer;
    _Childs :array[0..1]of TSymIdent;
    _NextFree : TSymIdent;
  protected
    FParent   :TScope;
  public
    NextSym:TSymIdent;
    BaseUnit : TBaseUnit;
    Directive :(drNone,drNew,drVirtual,drOverride,drAbstract);
    procedure AddOverload(AFunc:TSymIdent);
    function IsVirtualFunc: boolean;
    function FindSignature(AFunc: TFuncType; var AOut: TSymIdent): boolean;
    constructor Create;virtual;
    property Parent :TScope read FParent;
    function Clone():TSymIdent;
    procedure SetModifiers(AModifiers: TDclModifiers);
  end;

  TSymTyped = class(TSymIdent)
  protected
    function CreateType():TDataType;virtual;
  public
    constructor Create();override;
    destructor Destroy();override;
    procedure SetDataType(const Value: TDataType);override;
  end;

  TScope= class(TSymTyped)
  protected
     _Tree :TSymIdent;
     _List :TQSList;
     _Free :TSymIdent;
    function GetCount: integer;
    function GetSymbol(index: integer): TSymIdent;
    function FindNode(const Key :string;AHash:integer):PSymIdent;virtual;
    function InternalFindMember(ASearch: TSymSearchList;AContext:TScope ):boolean;virtual;
    function IsVisible(AContext: TScope; AItem: TSymIdent): boolean;virtual;
    function CreateType():TDataType;override;
    function _InternalFind(ASearch: TSymSearchList): boolean;virtual;
  public
    DefaultVisibility:TVisLevel;
    constructor Create();override;
    destructor Destroy();override;
    function IsParentOf(AItem: TSymIdent): boolean;virtual;
    function Find(ASearch: TSymSearchList): boolean;virtual;
    function FindMember(ASearch: TSymSearchList;AContext:TScope):boolean;overload;
    function FindMember(const AName:string;var AOut:TSymIdent):boolean; overload;
    function NewSymbol(const ANameKey:string;ABaseClass:TSymBaseClass):TSymIdent; overload;
    function NewSymbol(ABaseClass: TSymBaseClass): TSymIdent; overload;
    function Allocate(AItem:TExpr):integer;virtual;
    property Count :integer read GetCount;
    property Symbols[index:integer]:TSymIdent read GetSymbol;
  end;

  TAllocDeclStmt =class(TScope)
  public
    DefaultVarClass:TObjLocation;
    function Allocate(AItem:TExpr):integer;override;
  end;
  TAllocDeclStmtClass = class of TAllocDeclStmt;

  TCodeBlock = class(TAllocDeclStmt)
  protected
    function IsVisible(AContext: TScope; AItem: TSymIdent): boolean;override;
  end;

  TFuncBlockStmt =class(TCodeBlock)
  protected
    FHeader:TSymIdent;
    procedure SetHeaderInf(const Value: TSymIdent);
  public
    Code:TStmt;
    Epilogue:TStmt;// only to get line number
    LocalsVarCount:integer;
    ReturnExpr:TSymIdent;
    SelfExpr:TSymIdent;
    property Header:TSymIdent read FHeader write SetHeaderInf;
    function Allocate(AItem:TExpr):integer;override;
  end;

  TFuncHeaderStmt =class(TAllocDeclStmt)
  protected
    function CreateType():TDataType;override;
  end;

  TEnumStmt =class(TAllocDeclStmt)
  protected
    function CreateType():TDataType;override;
  public
    procedure SetTypeBase(ADataType:TDataType);
  end;

  TMemberStmt = class(TAllocDeclStmt)
  end;

  TFieldType = class(TMemberStmt)
  public
    procedure Validate;virtual;
  end;

  TStructStmt =class(TFieldType)
  protected
    function CreateType():TDataType;override;
  public
    procedure Validate;override;
  end;

  TUnionStmt =class(TStructStmt)
  public
    procedure Validate;override;
  end;

  TUnit =class;

  TUnitsList=class(TQSObjList)
  public
    function GetUnit(AIdx:integer):TUnit;
    function UnitIndex(const AName:string):integer;
  end;

  TUsingScope = class(TAllocDeclStmt)    // for test
  protected
    FList:TUnitsList;
    function InternalFindMember(ASearch: TSymSearchList;AContext:TScope ):boolean;override;
  public
    LookInNames:boolean;
    constructor Create();override;
    destructor Destroy();override;
    procedure Add(AType:TMemberStmt);
  end;

  TUses=class(TUsingScope)
  public
    constructor Create();override;
  end;

  TBaseUnit=class(TMemberStmt)
  protected
    FUsesList:TUses;
    FCodeList:TStmtList;
    FFuncList:TQSList;
  public
    constructor Create();override;
    destructor Destroy();override;
    procedure AddUnit(AUnit: TUnit);virtual;
    property CodeList:TStmtList read FCodeList;
    property FuncList:TQSList read FFuncList;
    property UsesList:TUses read FUsesList;
  end;

  TUnit=class(TBaseUnit)
  protected
    LocalUsesList:TUses;
    Localdcls:TScope;
    FImpSection:boolean;
    function FindNode(const Key: string;AHash: integer): PSymIdent;override;
    function _InternalFind(ASearch: TSymSearchList): boolean;override;
  public
    constructor Create();override;
    destructor Destroy();override;
    procedure ToggleToImplementation();
    procedure AddUnit(AUnit: TUnit);override;
    function IsInUses(AUnit:TUnit):boolean;
  end;

  TMainUnit=class(TBaseUnit)
  end;

  TInheritedType = class(TFieldType)
  protected
    function InternalFindMember(ASearch: TSymSearchList;AContext: TScope):boolean;override;
    function IsVisible(AContext:TScope;AItem:TSymIdent):boolean;override;
    function InternalFindInherited(ASearch: TSymSearchList;AContext:TScope ):boolean;virtual;
    function GetAncestor():TInheritedType;virtual;
  public
    function IsAncestorOf(AInhType: TInheritedType): boolean;
    function IsInheritedFrom(AInhType: TInheritedType): boolean;
    function IsScopeInheritedFrom(AScope: TScope): boolean;
    function FindInheritedMember(ASearch: TSymSearchList): boolean;
  end;

  TInterfaceStmt = class(TInheritedType)
  protected
    function CreateType():TDataType;override;
    function GetAncestor():TInheritedType;override;
  public
    Ancestor: TInterfaceStmt;
    procedure Validate;override;
    function Support(AInterface: TDataType):boolean;
  end;
  TClassStmt = class;
  TIntrfsList =class;

  TIntrfImplementation=class(TSymIdent)
  private
   FMType:TInterfaceStmt;
  public
   Table:TQSList;
   Implementator:TClassStmt;
   constructor Create();override;
   destructor Destroy;override;
   property MType:TInterfaceStmt read FMType;
   procedure SetDataType(const Value: TDataType);override;
  end;

  TIntrfsList=class(TQSObjList)
  public
    function GetItem(AIdx:integer):TIntrfImplementation;
    function InterfaceExists(AInterface: TDataType;var AOut:TIntrfImplementation):boolean;
    function GetIntrf(AInterface: TDataType): TIntrfImplementation;
  end;

  TClassStmt = class(TInheritedType)
  protected
    FVirtualMembers:TQSList;
    FIntrfsTables:TIntrfsList;
    function CreateType():TDataType;override;
    function GetAncestor():TInheritedType;override;
    function MakeIntrfEntry(AInterface: TDataType): TIntrfImplementation;
  public
    VTable:TSymIdent;
    IntrfsTable:TSymIdent;
    FUsedIntrfs:TIntrfsList;
    Ancestor:TClassStmt;
    constructor Create();override;
    destructor Destroy();override;
    property VirtualMembers:TQSList read  FVirtualMembers;
    property IntrfsTables:TIntrfsList read  FIntrfsTables;
    procedure Validate;override;
    procedure WriteInternalSymboles();
    function Support(AInterface: TDataType;var AOut:TIntrfImplementation):boolean;
    procedure AddInterface(AInterface: TDataType);
    function UpdateIntrfFuncEntry(AImpl:TIntrfImplementation;AFunc: TSymIdent):boolean;
    function SupportIUnknown: boolean;
  end;

  var
    symidx:integer;
implementation
uses UMsg;

function HashOf(const Key: string):integer;
var
  I:integer;
  S:string;
begin
  S :=UpperCase(Key);
  Result := 0;
  for I := 1 to Length(S) do
      Result := (Result shl 3) xor Result xor Ord(S[I]);
end;
{ TSymIdent }

procedure TSymIdent.AddOverload(AFunc: TSymIdent);
var
 Sym:TSymIdent;
begin
   Sym :=Self;
   while Sym.NextSym<> nil do
     Sym := Sym.NextSym;
   Sym.NextSym := AFunc;
end;

constructor TSymIdent.Create;
begin
end;

procedure TSymIdent.SetModifiers(AModifiers:TDclModifiers);
begin
   if dmPrivate in AModifiers then
     Visibility := vsPrivate
   else if dmProtected in AModifiers then
     Visibility := vsProtected
   else if dmLocal in AModifiers then
     Visibility := vsLocal
   else if dmLocalProtected in AModifiers then
     Visibility := vsLocalProtected
   else if dmPublic in AModifiers then
     Visibility := vsPublic
   else
     Visibility := Parent.DefaultVisibility;

   if dmVirtual in AModifiers then
     Directive := drVirtual
   else if dmOverride in AModifiers then
     Directive := drOverride
   else if dmAbstract in AModifiers then
     Directive := drAbstract
   else if dmNew in AModifiers then
     Directive := drNew;

   if dmReadonly in AModifiers then
      AccessType := qoReadOnly;
end;

function TSymIdent.IsVirtualFunc: boolean;
begin
   Result := (ObjLocation = olCode) and (Directive in [drVirtual,drOverride,drAbstract]);
end;

function TSymIdent.FindSignature(AFunc:TFuncType;var AOut:TSymIdent):boolean;
begin
   AOut := Self;
   repeat
      Result := AFunc.IsSignatureEqual(AOut.DataType,False);
      if Result then
         break;
      AOut:=AOut.NextSym;
   until AOut=nil;
end;

constructor TScope.Create;
begin
  inherited;
  _List :=TQSList.Create;
  DefaultVisibility := vsPublic;
end;

destructor TScope.Destroy;
var
  P,B:TSymIdent;
begin
   P := _Free;
   while P <> nil do
   begin
      B := P._NextFree;
      P.Free;
      P := B;
   end;
   _List.Free;
  inherited;
end;

function TScope.FindNode(const Key: string;AHash: integer): PSymIdent;
var
 N:Cardinal;
begin
    Result:=@_Tree;
    N:=AHash;
    repeat
      if (Result^ = nil)then
         break
      else if(Result^._HashCode= AHash)
           and Sametext(Result^.FName,Key)then
             break
      else
         Result :=@Result^._Childs[N and 1];
      N := ((N shl 1) or (N shr(SizeOf(N) * 8 - 1)));
    until False;
end;

function TScope.GetCount: integer;
begin
   Result := _List.Count;
end;

function TScope.GetSymbol(index: integer):TSymIdent;
begin
   Result := _List[index];
end;

function TSymIdent.Clone: TSymIdent;
begin
   Result := BaseUnit.NewSymbol(TSymIdent);
   Result.Assign(Self);
   Result.Directive:= Directive;
   Result.Visibility := Visibility;
   Result.FParent :=FParent;
   inc(symidx)
end;

{ TScope }

function TScope.InternalFindMember(ASearch: TSymSearchList;
             AContext:TScope):boolean;
var
 P:TSymIdent;
begin
    P := FindNode(ASearch.Text,ASearch.FHash)^;
    Result := P<> nil;
    if not Result then
       Exit;
    Result := False;
    while P<> nil do
    begin
        if IsVisible(AContext,P) then
        begin
           ASearch.Add(P);
           Result := True;
        end;
        P :=P.NextSym;
    end;
end;

function TScope.IsVisible(AContext:TScope;AItem:TSymIdent):boolean;
begin
    if (AItem.Visibility =vsPublic)or(AContext = Self) then
       Result := True
    else if AItem.Visibility in [vsLocal,vsLocalProtected] then
       Result :=Assigned(AContext) and (AContext.BaseUnit = BaseUnit)
    else {Private}
       Result := IsParentOf(AContext);
end;

function TScope.FindMember(ASearch: TSymSearchList;
  AContext: TScope): boolean;
begin
    ASearch.Clear;
    Result := InternalFindMember(ASearch,AContext);
end;

function TScope.FindMember(const AName:string;var AOut:TSymIdent):boolean;
var
  P:PSymIdent;
  H:integer;
begin
    H:=HashOf(AName);
    AOut := nil;
    P := FindNode(AName,H);
    Result := P^<> nil;
    if not Result then
       Exit;
    AOut := P^;
end;

function TScope.IsParentOf(AItem: TSymIdent): boolean;
begin
   Result :=True;
   while AItem <> nil do
   begin
      if AItem.Parent = Self then
         Exit;
       AItem:=AItem.Parent;
   end;
   Result :=False;
end;

function TScope.Allocate(AItem: TExpr): integer;
begin
   raise ECompException.Create('empty list');
end;

function TScope.CreateType: TDataType;
begin
    Result :=TTypeMembers.Create;
end;

function TScope.Find(ASearch: TSymSearchList):boolean;
var
   Obj:TScope;
begin
    ASearch.Clear;
    Obj  := Self;
    repeat
        Result := Obj._InternalFind(ASearch);
        if Result then
         Exit;
        Obj:= Obj.Parent;
    until Obj = nil;
    Result := False;
end;

function TScope._InternalFind(ASearch: TSymSearchList): boolean;
begin
   Result := InternalFindMember(ASearch,Self);
end;

{ TBaseUnit }

constructor TBaseUnit.Create;
begin
  inherited;
  FCodeList:=TStmtList.Create;
  FFuncList:=TQSList.Create;
  BaseUnit :=Self;
  FUsesList:=TUses.Create;
  FParent:=FUsesList;
  Address := -1;
end;

destructor TBaseUnit.Destroy;
begin
  FUsesList.Free;
  FFuncList.Free;
  FCodeList.Free;
  inherited;
end;

procedure TBaseUnit.AddUnit(AUnit: TUnit);
begin
   if (AUnit = Self) or (FUsesList.FList.IndexOf(AUnit)<> -1) then
      raise ECompException.Create('Unit insert error');
   FUsesList.Add(AUnit);
end;

function TScope.NewSymbol(const ANameKey: string;
  ABaseClass: TSymBaseClass): TSymIdent;
var
  P:PSymIdent;
  H:integer;
begin
   H:=HashOf(ANameKey);
   P:=FindNode(ANameKey,H);
   if P^ <> nil then
   begin
      raise ECompException.Createfmt('item exists %s',[ANameKey]);
   end;
   Result := NewSymbol(ABaseClass);
    with Result do
    begin
      _HashCode := H;
      FName     := ANameKey;
    end;
    P^:=Result;
    _List.Add(Result); // liste des noms
end;

function TScope.NewSymbol(ABaseClass: TSymBaseClass): TSymIdent;
begin
   Result :=ABaseClass.Create;
   with Result do
    begin
      BaseUnit := Self.BaseUnit;
      FParent   := Self;
      _NextFree :=_Free;
    end;
    _Free :=Result;
end;

{ TUnit }
procedure TUnit.AddUnit(AUnit: TUnit);
begin
   if FImpSection then
   begin
     if FUsesList.FList.IndexOf(AUnit)<>-1 then
       raise ECompException.Create('circular reference');
     LocalUsesList.Add(AUnit);
   end else begin
     if AUnit.IsInUses(Self)then
        raise ECompException.Create('circular reference');
     inherited AddUnit(AUnit);
   end;
end;

constructor TUnit.Create;
begin
  inherited;
  LocalUsesList:=TUses.Create;
  Localdcls:=TScope.Create;
end;

destructor TUnit.Destroy;
begin
  Localdcls.Free;
  LocalUsesList.Free;
  inherited;
end;

function TUnit.FindNode(const Key: string; AHash: integer): PSymIdent;
begin
   Result := nil;
   if FImpSection then
      Result := Localdcls.FindNode(Key,AHash);
   if (Result = nil)or(Result^ = nil) then
      Result := inherited FindNode(Key,AHash);
end;

function TUnit.IsInUses(AUnit: TUnit): boolean;
var
 I:integer;
 U:TUnit;
begin
   for I := 0 to FUsesList.FList.Count-1 do //only interface section
   begin
     U:=TSymIdent(FUsesList.FList[I]) as TUnit;
     if (U = AUnit)or U.IsInUses(AUnit) then
     begin
        Result := True;
        Exit;
     end;
   end;
   Result := False;
end;

procedure TUnit.ToggleToImplementation;
begin
  FImpSection := True;
end;

function TUnit._InternalFind(ASearch: TSymSearchList): boolean;
begin
   Result := True;
   if FImpSection then
   begin
      if Localdcls.FindMember(ASearch,Localdcls)
         or LocalUsesList.FindMember(ASearch,LocalUsesList) then
            Exit;
   end;
   Result := inherited _InternalFind(ASearch);
end;

{ TCodeBlock }

function TCodeBlock.IsVisible(AContext: TScope; AItem: TSymIdent): boolean;
begin
   Result := AContext = Self;
   if not Result then
      Result :=IsParentOf(AContext);
end;

{ TSymSearchList }

procedure TSymSearchList.Add(Sym: TSymIdent);
begin
  if FMutch=nil then
  begin
     if Sym.NextSym <> nil then
        FMutch := Sym.Clone
     else
        FMutch := Sym
  end else begin
     if FMutch._NextFree=nil then
        FMutch := FMutch.Clone();
     FMutch.AddOverload(Sym.Clone());
  end;
end;

procedure TSymSearchList.Clear;
begin
   FMutch :=nil;
end;

procedure TSymSearchList.SetText(const Value: string);
begin
  FText := Value;
  FHash :=HashOf(Value);
end;

{ TUsingScope }

procedure TUsingScope.Add(AType: TMemberStmt);
begin
   FList.Add(AType);
end;

constructor TUsingScope.Create;
begin
  inherited;
  FList:=TUnitsList.Create;
  FList.OwnObjs :=false;   //  a tester
end;

destructor TUsingScope.Destroy;
begin
  FList.Free;
  inherited;
end;

function TUsingScope.InternalFindMember(ASearch: TSymSearchList;
  AContext: TScope): boolean;
var
 I:integer;
begin
  Result := inherited InternalFindMember(ASearch,AContext);
  if Result then
    Exit;

  if LookInNames then
   for I := 0 to FList.Count-1 do
   with FList.GetUnit(I) do
      if SameText(Name,ASearch.Text) then
      begin
        ASearch.Add(FList.GetUnit(I));
        Result := True;
        Exit;
      end;

   for I := FList.Count-1 downto 0 do
   with FList.GetUnit(I) do
    begin
        if FList.GetUnit(I).InternalFindMember(ASearch,AContext) then
        begin
            Result := True;
           // Exit;      ambiguité
        end;
    end;
end;

{ TUses }

constructor TUses.Create;
begin
  inherited;
  LookInNames :=true;
end;

{ TSymTyped }

constructor TSymTyped.Create;
begin
  inherited;
  DataType := CreateType();
end;

function TSymTyped.CreateType: TDataType;
begin
  Result := nil;
end;

procedure TSymTyped.SetDataType(const Value: TDataType);
begin
  inherited SetDataType(Value);
  if (Value <> nil)and(Value.SymbInfo =nil) then
     Value.SymbInfo := Self;
end;

destructor TSymTyped.Destroy;
begin
  FDataType.Free;
  inherited;
end;

{ TAllocDeclStmt }

function TAllocDeclStmt.Allocate(AItem: TExpr): integer;
begin
   Result := TTypeMembers(DataType).Members.AddExpr(AItem);
   AItem.Address :=Result;
   if AItem.ObjLocation  = olNone then
      AItem.ObjLocation := DefaultVarClass;
end;

{ TFuncBlockStmt }

function TFuncBlockStmt.Allocate(AItem: TExpr): integer;
begin
     Result := inherited Allocate(AItem);
     AItem.Address:=LocalsVarCount;
     inc(LocalsVarCount);
end;

procedure TFuncBlockStmt.SetHeaderInf(const Value: TSymIdent);
var
  I:integer;
  SymExpr:TSymbolExpr;
begin
     if FHeader <> nil then
        raise ECompException.Create('function header is not empty');
     FHeader := Value;
     if Value.IsMethod() then
     begin
         SelfExpr := NewSymbol('self',TSymIdent);
         with SelfExpr do
         begin
            ObjLocation:=olParam;
            Address:= LocalsVarCount;
            inc(LocalsVarCount);
            SetDataType(PtrType.DataType);
            Used := True;
         end;
     end;
    // if not FHeader.DataType.Dest.IsVoidType then
     begin
         ReturnExpr := NewSymbol('result',TSymIdent);
         with ReturnExpr do
         begin
            ObjLocation:=olRet;
            Address:= LocalsVarCount;
            inc(LocalsVarCount);
            QureyKind := atReference;
            SetDataType(FHeader.DataType.Dest);
         end;
     end;
     with TFuncType(FHeader.DataType).Members do
       for I := 0 to Count -1 do
       begin
         SymExpr :=TSymbolExpr(GetExpr(I));
         with NewSymbol(SymExpr.Name,TSymIdent)do
         begin
            Assign(SymExpr);
            Address:= LocalsVarCount;
            Used:=True;
            inc(LocalsVarCount);
         end;
       end;
end;

{ TFuncHeaderStmt }

function TFuncHeaderStmt.CreateType: TDataType;
begin
  Result :=TFuncType.Create;
  Result.SeBaseTypeProps(tcFuncType,[it32Bit],SIZEOFPOINTER,nil);
end;

{ TENumStmt }

function TEnumStmt.CreateType: TDataType;
begin
  Result :=TTypeMembers.Create;
  Result.TypeClass :=tcEnum;
end;

procedure TEnumStmt.SetTypeBase(ADataType: TDataType);
begin
    if not ADataType.IsIntType then                // warning for test
      raise ECompException.Create('int type expected');
    FDataType.SeBaseTypeProps(tcEnum,ADataType.BitsClass,ADataType.TypeSize,nil);
end;

{ TFieldType }

procedure TFieldType.Validate;
begin
end;

{ TStructStmt }

function TStructStmt.CreateType: TDataType;
begin
  Result :=TTypeMembers.Create;
  Result.TypeClass :=tcStruct;
end;

procedure TStructStmt.Validate;
var
 I:integer;
 dtm:TTypeMembers;
 Sz,fSz,SzBits,Offst:integer;
 BitField:TBitField;
 dtExpr:TExpr;
begin
  dtm :=TTypeMembers(DataType);
  Sz    := 0;
  SzBits:= 0;
  for I := 0 to dtm.Members.Count -1 do
  begin
      dtExpr :=dtm.Members.GetExpr(I);
      fSz :=dtExpr.DataType.TypeSize;
      if dtExpr.DataType is TBitField then
      begin
         BitField :=dtExpr.DataType as TBitField;
         if SzBits+BitField.BitsCount > INT_UNIT * ALLOC_UNIT then
         begin
            Sz :=Sz + INT_UNIT;
            SzBits := 0;
         end;
         BitField.BitsOffset :=SzBits;
         SzBits := SzBits+BitField.BitsCount;
         Offst :=Sz;
      end else begin
         if SzBits <> 0 then
            Sz :=Sz+UnSignedValueSize((1 shl SzBits)-1);
         SzBits :=0;
         Offst :=Sz;
         Sz :=Sz + fSz;
      end;
     // dtExpr.Address := I;
      dtExpr.Address :=Offst;
  end;
  if SzBits <> 0 then
     Sz :=Sz+UnSignedValueSize((1 shl SzBits)-1);
  dtm.TypeSize  := Sz;
  dtm.TypeClass :=tcStruct;
end;

{ TUnionStmt }

procedure TUnionStmt.Validate;
var
 I:integer;
 dtm:TTypeMembers;
 Sz:integer;
begin
  dtm :=TTypeMembers(DataType);
  Sz := 0;
  for I := 0 to dtm.Members.Count -1 do
  with dtm.Members.GetExpr(I)do
   begin
      Address :=0;
      if Sz < DataType.TypeSize then
         Sz :=DataType.TypeSize;
   end;
  dtm.TypeSize  := Sz;
  dtm.TypeClass :=tcStruct;
end;

{ TUnitsList }

function TUnitsList.GetUnit(AIdx: integer): TUnit;
begin
   Result := TUnit(inherited Items[AIdx]);
end;

function TUnitsList.UnitIndex(const AName: string): integer;
begin
  for Result := 0 to Count -1 do
   if Sametext(GetUnit(Result).Name,AName) then
      Exit;
  Result := -1;
end;

{ TInheritedType }

function TInheritedType.InternalFindMember(
   ASearch: TSymSearchList; AContext: TScope): boolean;
begin
  Result := inherited InternalFindMember(ASearch,AContext);
  if Result then
     Exit;
  Result :=InternalFindInherited(ASearch,AContext);
end;

function TInheritedType.IsVisible(AContext: TScope;AItem: TSymIdent): boolean;
begin
   Result:= inherited IsVisible(AContext,AItem);
   if not Result then
     if AItem.Visibility in[vsProtected,vsLocalProtected]then
        Result :=IsScopeInheritedFrom(AContext)
     else
        Result := False;
end;

function TInheritedType.FindInheritedMember(ASearch: TSymSearchList): boolean;
begin
      ASearch.Clear;
      Result:=InternalFindInherited(ASearch,Self);
end;

function TInheritedType.InternalFindInherited(ASearch: TSymSearchList; AContext: TScope): boolean;
var
  Ans:TInheritedType;
begin
   Ans := GetAncestor();
   Result := Ans <> nil;
   if Result then
      Result := Ans.InternalFindMember(ASearch,AContext);
end;

function TInheritedType.IsInheritedFrom(AInhType: TInheritedType): boolean;
var
 Ans:TInheritedType;
begin
   Ans := GetAncestor();
   Result := Ans <> nil;
   if Result then
      Result := (Ans = AInhType)or Ans.IsInheritedFrom(AInhType)
end;

function TInheritedType.IsScopeInheritedFrom(AScope: TScope): boolean;
begin
   //  Result :=True;
     while AScope <> nil do
     begin
        if AScope is TInheritedType then
        begin
          Result :=TInheritedType(AScope).IsInheritedFrom(Self);
          if Result then
             Exit;
        end;
        AScope:=AScope.Parent;
     end;
     Result :=False;
end;

function TInheritedType.IsAncestorOf(AInhType: TInheritedType): boolean;
begin
    Result:= AInhType.IsInheritedFrom(Self);
end;

function TInheritedType.GetAncestor: TInheritedType;
begin
   Result := nil;
end;

{ TInterfaceStmt }

function TInterfaceStmt.CreateType: TDataType;
begin
  Result :=TInterfaceType.Create;
  Result.TypeClass :=tcInterface;
  Result.TypeSize := SIZEOFPOINTER;
 // Randomize();
  TInterfaceType(Result).IID := Random(MAXINT);
end;

function TInterfaceStmt.GetAncestor: TInheritedType;
begin
  Result := Ancestor;
end;

function TInterfaceStmt.Support(AInterface: TDataType): boolean;
var
  Intrf:TInterfaceStmt;
begin
   Result :=True;
   Intrf := Self;
   if AInterface.IsInterface then
     repeat
        if TInterfaceType(Intrf.DataType).IID = TInterfaceType(AInterface).IID then
           Exit;
        Intrf := Intrf.Ancestor;
     until Intrf = nil;
   Result :=False;
end;

procedure TInterfaceStmt.Validate;
var
 I:integer;
 dtm:TInterfaceType;
 Sz,Len:integer;
 B:TSymIdent;
begin
  dtm :=TInterfaceType(DataType);
  Sz := 0;
  Len := 0;
  if Ancestor <> nil then
    with TInterfaceType(Ancestor.DataType) do
    begin
       Sz := Table_Size;
       Len := Members.Count;
    end;
  Address := Len;
  for I:= 0 to Count -1 do
  begin
     B := Symbols[I];
     repeat
       TFuncType(B.DataType).VirtualOffset :=Len;
       Allocate(B);
       B.Address :=Sz;
       Sz :=Sz + SIZEOFPOINTER;
       Inc(len);
       B:= B.NextSym;
     until B=nil;
  end;
  //datatype.TypeSize:=sz;// for test
  dtm.Table_Size  := Sz;
end;

{ TIntrfImplementation }

constructor TIntrfImplementation.Create;
begin
  inherited;
  Table:=TQSList.Create;
end;

destructor TIntrfImplementation.Destroy;
begin
  Table.Free;
  inherited;
end;

procedure TIntrfImplementation.SetDataType(const Value: TDataType);
begin
  inherited;
  FMType:= TInterfaceStmt(Value.SymbInfo);
  Table.Count := TInterfaceType(Value).Members.Count;
end;
{ TIntrfsList }

function TIntrfsList.GetItem(AIdx: integer): TIntrfImplementation;
begin
   Result := Items[AIdx]
end;

function TIntrfsList.InterfaceExists(AInterface: TDataType;var AOut:TIntrfImplementation):boolean;
var
 i:integer;
begin
  Result := True;
  if AInterface.IsInterface() then
    for I := 0 to Count -1 do
    begin
      AOut := GetItem(I);
      if TInterfaceType(AOut.MType.DataType).IID= TInterfaceType(AInterface).IID then
         Exit;
    end;
  Result := False;
  AOut := nil;
end;

function TIntrfsList.GetIntrf(AInterface: TDataType):TIntrfImplementation;
begin
   if not InterfaceExists(AInterface,Result)then
      raise ECompException.CreateRes(@UNSUPPORTED_INTERFACE);
end;

{ TClassStmt }

procedure TClassStmt.WriteInternalSymboles;
// do not call this from TClassStmt.Create since: baseunit = nil
var
 Sym:TSymIdent;
begin
  Sym := NewSymbol(TSymIdent); // self;
  Sym.SetDataType(PtrType.DataType);
  Allocate(Sym);
  VTable := NewSymbol('vTable',TSymIdent);
  VTable.SetDataType(PtrType.DataType);
  VTable.Visibility := vsPublic;
  IntrfsTable := NewSymbol('IntrfsTable',TSymIdent);
  IntrfsTable.SetDataType(PtrType.DataType);
  IntrfsTable.Visibility := vsPublic;
end;

constructor TClassStmt.Create;
begin
  inherited;
  FVirtualMembers:=TQSList.Create;
  FIntrfsTables:=TIntrfsList.Create;
  FUsedIntrfs := TIntrfsList.Create;
end;

function TClassStmt.CreateType: TDataType;
begin
  Result :=TClassType.Create;
  Result.TypeClass :=tcClass;
  Result.TypeSize := SIZEOFPOINTER;
end;

destructor TClassStmt.Destroy;
begin
  FUsedIntrfs.Free;
  FIntrfsTables.Free;
  FVirtualMembers.Free;
  inherited;
end;

procedure TClassStmt.Validate;
var
 I:integer;
 dtm:TClassType;
 Sz:integer;
 B:TSymIdent;
 Intrf:TInterfaceStmt;
 Impl:TIntrfImplementation;
begin
  dtm :=TClassType(DataType);
  Sz := 0;
  if Ancestor <> nil then
  begin
     Address   := Ancestor.VirtualMembers.Count;
     Sz := TClassType(Ancestor.DataType).Instance_Size -SIZEOFPOINTER;
     for I := 0 to Ancestor.VirtualMembers.Count-1 do
     begin
        B := Ancestor.VirtualMembers[I];
        VirtualMembers.Add(B);
     end;
  end;
  for I := 0 to FUsedIntrfs.Count-1 do
  begin
     // Allocate(FUsedIntrfs.GetItem(I));
      Intrf := TIntrfImplementation(FUsedIntrfs[I]).MType.Ancestor;
      while Intrf <> nil do
      begin
         if not FIntrfsTables.InterfaceExists(Intrf.DataType,Impl) then
            MakeIntrfEntry(Intrf.DataType);
         Intrf := Intrf.Ancestor;
      end;
  end;
  for I := 0 to dtm.Members.Count -1 do
  begin
     B := dtm.Members.GetExpr(I) as TSymIdent;
     B.Address := Sz;
     Sz :=Sz + B.DataType.TypeSize;
  end;
  //datatype.TypeSize := Sz;//self ptr for test
  dtm.Instance_Size := Sz ;
end;

function TClassStmt.GetAncestor: TInheritedType;
begin
    Result := Ancestor;
end;

function TClassStmt.Support(AInterface: TDataType;var AOut:TIntrfImplementation):boolean;
var
  Cls:TClassStmt;
begin
  Cls := Self;
  repeat
      Result := Cls.FUsedIntrfs.InterfaceExists(AInterface,AOut);
      if Result then
         Exit;
      Cls:= Cls.Ancestor;
  until Cls = nil;
end;

function TClassStmt.SupportIUnknown():boolean;
var
  Cls:TClassStmt;
  I:integer;
  Impl:TIntrfImplementation;
begin
  Result := True;
  Cls := Self;
  repeat
      for I := 0 to Cls.FUsedIntrfs.Count-1 do
      begin
        Impl := Cls.FUsedIntrfs.GetItem(I);
        if TInterfaceType(Impl.DataType).IID = IUNKNOWN_INTF_IID then
           Exit;
      end;
      Cls:= Cls.Ancestor;
  until Cls = nil;
  Result := False;
end;

procedure TClassStmt.AddInterface(AInterface: TDataType);
var
 Impl:TIntrfImplementation;
begin
  if FUsedIntrfs.InterfaceExists(AInterface,Impl)then
     raise ECompException.Create('interface exists');
  Impl :=MakeIntrfEntry(AInterface);
  FUsedIntrfs.Add(Impl);
  Allocate(Impl);
end;

function TClassStmt.MakeIntrfEntry(AInterface: TDataType):TIntrfImplementation;
var
 Sym:TSymIdent;
begin
   Sym := NewSymbol(TIntrfImplementation);
   Result := TIntrfImplementation(Sym);
   Result.Implementator := Self;
   Result.SetDataType(AInterface);
   FIntrfsTables.Add(Result);
end;

function TClassStmt.UpdateIntrfFuncEntry(AImpl: TIntrfImplementation;AFunc: TSymIdent): boolean;
var
 Sym,Fn:TSymIdent;
 Idx:integer;
begin
   with AImpl do
    if MType.FindMember(AFunc.Name,Sym)
       and Sym.FindSignature(TFuncType(AFunc.DataType),Fn)then
        begin
           // calc relative offset
           Idx :=TFuncType(Fn.DataType).VirtualOffset-MType.Address;
           Table[Idx]:=  AFunc;
           Result := True;
           Exit;
        end;
   Result := False;
end;




end.
