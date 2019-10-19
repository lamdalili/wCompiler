unit UGenerator;

interface
uses
  Windows, SysUtils, Classes,Utils,dialogs,UCommon;
type
   TByteCode=(bcNone,
    bcComp,bcAddr,bcDeRef,
    bcAnd,bcOr,bcXor,
    bcShl,bcShr,

    {unsigned integer}
    bcMinus,
    bcAdd,bcSub,bcMul,bcDiv,bcModulo,
    bcEqu,bcLess,bcGr,bcNotequ,bcLessEqu,bcGrEqu,

    {signed integer}
    bciMinus,
    bciAdd,bciSub,bciMul,bciDiv,bciModulo,
    bciLess,bciGr,bciLessEqu,bciGrEqu,

    {float}
    bcfMinus,
    bcfAdd,bcfSub,bcfMul,bcfDiv,
    bcfEqu,bcfLess,bcfGr,bcfNotequ,bcfLessEqu,bcfGrEqu,

    bcflt_To_Int,bcInt_To_flt,
    bc_Is_Cls,bc_Is_Intrf,
    bc_z,
    bcLiteral,
    bcLoadlabel,
    bcLoad_i8,  bcLoad_u8,
    bcLoad_i16, bcLoad_u16,
    bcLoad_i32, bcLoad_u32,
    bcLoad_64,

    bcSave_i8,  bcSave_u8,
    bcSave_i16, bcSave_u16,
    bcSave_i32, bcSave_u32,
    bcSave_64,

    bcLoad_flt, bcSave_flt,
    bcBitsRead,bcBitsWrite,bcRegToTmp,  // bitsfield
    bcConstructor,
    bcPush,bcPop,bcFunEnter,bcFunLeave,
    bcCall,bcvCall,bciCall, // virtual call;interface call
    bcJump,bcRet,bcHalt,
    bcParam,bcResultAddr,
    bcCondJump,
    bcGetCls,bcGetIntrf,

    // error handler
    bcHandlerRet,bcClearErr,bcReadErr,
    bcEnterHandler,
    bcExitHandler,bcPopErrCode,
    bcRaiseError,bcReRaise,
    // dbg
    bcPrint,bcLineNumber
    );
   TRegDest=(rgNone,rgReg1,rgReg2,rgReg3);
   TDispType= (ds_Unknown,ds_Char,ds_Bool,ds_Int,ds_Uint,ds_Float,ds_Ptr,ds_CharArray);
   TLocType= (vtNone,vtCode,vtLiteral,vtLocal,vtFrame,vtStatic);
   TMcLoc=record
     LocType:TLocType;
     Addr:integer;
     Unitidx:integer;
   end;
   TLoc = record
              kind:(vtVar,vtOffset,vtPtr,vtpOffset);
              Base:TMcLoc;
              Idx :TMcLoc;
           end;
   TCodeMc=packed record
     Bytecode:TByteCode;
     vReg:TRegDest;
     case integer of
       0:(Loc:TLoc);
       1:(OprdInt:integer);
       2:(Oprdflt:single);
   end;

   TByteRec=class
   public
      CodeMc:TCodeMc;
   end;

   TObjSymInfo=class
   public
     Loc:TLocType;
     Index:Integer;
     Size:integer;
     Value:integer;
   end;

   TBinObj=class;
   TUnitInfo=class
   public
     Name:string;
     Version:Integer;
     Link:TBinObj;
   end;

   TFuncEntry=class(TQSObjList)
  private
    function GetObjSymInfo(Tag: integer): TObjSymInfo;
    function FindSymbTag(ATag: integer): TObjSymInfo;
   public
     EntryTag:integer;
     CodeList:TQSObjList;
     function SymbTag(ATag,ASize: integer;ALoc:TLocType):TObjSymInfo;
     function GetSymbTag(ATag: integer):TObjSymInfo;
     function GetByteRec(Tag:integer):TByteRec;
   end;

   TBinObj=class
  private
    procedure UpdateLocation(var AbRec: TMcLoc);
    procedure ProcessLoc(var ALoc: TLoc);
    function PatchStaticLocation(const ASv :TMcLoc):integer;
   public
      GlobalSymbs:TFuncEntry;
      FuncsList:TQSObjList;
      Locals:TFuncEntry;
      UnitsRefs:TQSObjList;
      Codelength:integer;
      StaticData:TResBucket;
      Version:integer;
      lod:boolean;
      constructor Create();
      destructor Destroy();override;
      procedure NewFuncEntry();
      function UnitIndex(const AName: string): integer;
      function NewInstruction():TByteRec; overload;
      function NewInstruction(A:TByteCode):TByteRec;overload;
      procedure UpdateLabsAndFuncs(var ACodeStart: integer);
      procedure CalcStaticVars(var AVarsStart: integer);
      procedure LinkAndExport(Stream: TStream);
      procedure LoadFromStream(AStream:TStream);
      procedure SaveToStream(AStream:TStream);
      procedure CalcLocals(var AParamsSize, ALocalsSize: integer);
   end;
   function MakeBitsMask(StartBitIdx,EndBitIdx:integer;Value:boolean):integer;
function BcName(bc:TByteCode):string;
implementation
uses UNodesBase,typinfo;

function MakeBitsMask(StartBitIdx,EndBitIdx:integer;Value:boolean):integer;
var
 I:integer;
begin
   Result :=0;
   for I := 0 to ALLOC_UNIT*INT_UNIT-1 do
   begin
     if (I< StartBitIdx)or(I>=EndBitIdx)then
        Result := Result or (1 shl I);
   end;
   if Value then
      Result := not Result;
end;

function BcName(bc:TByteCode):string;
begin
  Result := GetEnumName(typeinfo(TByteCode),ord(bc));
end;

{ TFuncEntry }
function TFuncEntry.FindSymbTag(ATag: integer): TObjSymInfo;
var
 I:integer;
begin
  for I := 0 to Count-1 do
  begin
    Result := GetObjSymInfo(I);
     if (Result.Index= ATag) then
           Exit;
  end;
  Result := nil;
end;

function TFuncEntry.GetObjSymInfo(Tag: integer): TObjSymInfo;
begin
   Result := TObjSymInfo(Items[Tag]);
end;

function TFuncEntry.GetSymbTag(ATag: integer): TObjSymInfo;
begin
  Result := FindSymbTag(ATag);
  if Result = nil then
     raise ECompException.Create('invalid tag '+inttostr(ATag));
end;

function TFuncEntry.SymbTag(ATag, ASize: integer;ALoc: TLocType): TObjSymInfo;
begin
  Result := FindSymbTag(ATag);
  if Result <> nil then
    Exit;
  Result :=TObjSymInfo.Create;
  Add(Result);
  Result.Index :=ATag;
  Result.Size  :=ASize;
  Result.Loc  := ALoc;
end;

function TFuncEntry.GetByteRec(Tag: integer): TByteRec;
begin
   Result := TByteRec(CodeList.Items[Tag]);
end;

constructor TBinObj.Create;
begin
   GlobalSymbs:=TFuncEntry.Create;
   UnitsRefs:=TQSObjList.Create;
   FuncsList:=TQSObjList.Create;
   StaticData:=TResBucket.Create;
   GlobalSymbs.OwnObjs := True;
   UnitsRefs.OwnObjs := True;
   FuncsList.OwnObjs := True;
end;

destructor TBinObj.Destroy;
begin
  StaticData.Free;
  FuncsList.Free;
  UnitsRefs.Free;
  GlobalSymbs.Free;
  inherited;
end;

function TBinObj.UnitIndex(const AName: string):integer;
begin
  for Result := 0 to UnitsRefs.Count -1 do
   with TUnitInfo(UnitsRefs[Result])do
   if Sametext(Name,AName) then
      Exit;
  Result := -1;
end;

procedure TBinObj.NewFuncEntry;
begin
  Locals:=TFuncEntry.Create;
  Locals.OwnObjs :=True;
  FuncsList.Add(Locals);
  Locals.CodeList:=TQSObjList.Create;
  Locals.CodeList.OwnObjs :=True;
end;

function TBinObj.NewInstruction(): TByteRec;
begin
   Codelength:= Codelength +1;
   Result:=TByteRec.Create;
   Locals.CodeList.Add(Result);
end;

function TBinObj.NewInstruction(A: TByteCode): TByteRec;
begin
  Result := NewInstruction;
  Result.CodeMc.Bytecode:=A;
end;

function TBinObj.PatchStaticLocation(const ASv :TMcLoc):integer;
var
 Ob:TBinObj;
 i:integer;
 Unf:TUnitInfo;
begin
  Unf :=TUnitInfo(UnitsRefs[ASv.Unitidx]);
  Ob  :=Unf.Link;
  for  I := 0 to Ob.GlobalSymbs.Count -1 do
   with Ob.GlobalSymbs.GetObjSymInfo(i) do
    if (ASv.Addr =Index)and (ASv.LocType=Loc) then
    begin
       Result := Value;
       Exit;
    end;

  raise ECompException.Create('link error');
end;

procedure TBinObj.UpdateLocation(var AbRec: TMcLoc);
begin
    case AbRec.LocType of
       vtStatic:begin
           AbRec.Addr :=PatchStaticLocation(AbRec);
         end;
       vtCode:begin
           AbRec.Addr :=PatchStaticLocation(AbRec);
         end;
       vtLocal:begin
         ///  if not lod then
           AbRec.Addr := Locals.GetSymbTag(AbRec.Addr).Value;
         end;
       vtFrame:begin
          // if not lod then
           AbRec.Addr := Locals.GetSymbTag(AbRec.Addr).Value;
         end;
    end;
end;

procedure TBinObj.ProcessLoc(var ALoc: TLoc);
begin
    case ALoc.kind of
       vtOffset,vtpOffset:begin
            UpdateLocation(ALoc.Base);
            UpdateLocation(ALoc.Idx);
         end;
       vtPtr:begin
            UpdateLocation(ALoc.Base);
         end;
    else
      UpdateLocation(ALoc.Base);
      //  vtVar:
       //raise Exception.Create('Loc.kind error');
    end;
end;

procedure TBinObj.CalcStaticVars(var AVarsStart: integer);
var
 I:integer;
begin
 for I:=0 to  GlobalSymbs.Count-1 do
  with GlobalSymbs.GetObjSymInfo(I) do
  begin
    if Loc = vtStatic then
    begin
      value := AVarsStart;
      AVarsStart :=AVarsStart + Size;
    end;
  end;
end;

procedure TBinObj.CalcLocals(var AParamsSize,ALocalsSize:integer);
var
 I,J:integer;
 Fe:TFuncEntry;
begin
 for J:= 0 to FuncsList.Count -1 do
 begin
      AParamsSize := 0;
      ALocalsSize := 0;
      Fe :=TFuncEntry(FuncsList[J]);
      for I:= 0 to Fe.Count -1 do
       with Fe.GetObjSymInfo(I) do
        if Loc = vtLocal then
          begin
             value := ALocalsSize;
             ALocalsSize :=ALocalsSize+ Size;
          end;
      for I:= 0 to Fe.Count -1 do
       with Fe.GetObjSymInfo(I) do
         if Loc = vtFrame then
          begin
             value := AParamsSize- Size;
             AParamsSize :=value;
          end;
  end;
end;

procedure TBinObj.UpdateLabsAndFuncs(var ACodeStart: integer);
var
 I,J,M:integer;
 Mc:TByteRec;
begin
 M :=ACodeStart;
 for J:= 0 to FuncsList.Count -1 do
 begin
      Locals :=TFuncEntry(FuncsList[J]);
      GlobalSymbs.GetSymbTag(Locals.EntryTag).Value := ACodeStart;
      for I:= 0 to Locals.CodeList.Count -1 do
      begin
         Mc := Locals.GetByteRec(i);
         with Mc.CodeMc do
          case Bytecode of
              bcJump,bcLoadlabel,bcEnterHandler:
              begin
                 OprdInt := OprdInt + M;
              end;
          end;
         ACodeStart := ACodeStart +1;
      end;        
  end;
end;

procedure TBinObj.LinkAndExport(Stream:TStream);
var
 I,J:integer;
 Mc:TByteRec;
 Fe:TFuncEntry;
begin
 for J:= 0 to FuncsList.Count -1 do
 begin
      Fe :=TFuncEntry(FuncsList[J]);
      Locals  :=Fe;
      for I:= 0 to Fe.CodeList.Count -1 do
      begin
         Mc := Fe.GetByteRec(i);
         with Mc.CodeMc do
           case Bytecode of
              bcAddr,
              bcParam,bcResultAddr,
              bcLoad_i8,  bcLoad_u8,
              bcLoad_i16, bcLoad_u16,
              bcLoad_i32, bcLoad_u32,
              bcSave_i8,  bcSave_u8,
              bcSave_i16, bcSave_u16,
              bcSave_64,  bcLoad_64,
              bcLoad_flt, bcSave_flt,
              bcBitsRead,bcBitsWrite,
              bcSave_i32, bcSave_u32:ProcessLoc(Mc.CodeMc.Loc);
           end;
         Stream.Write(Mc.CodeMc,Sizeof(TCodeMc));
      end;
  end;

end;

procedure TBinObj.LoadFromStream(AStream: TStream);
var
 I,J:integer;
 Mc:TByteRec;
 Fe:TFuncEntry;
 UnitInf:TUnitInfo;
 LCount,Ccount:integer;
 sf:TObjSymInfo;
begin
 AStream.Read(LCount,SizeOf(Integer));
 for I:=0 to LCount-1 do
 begin
    sf :=TObjSymInfo.Create;
    GlobalSymbs.Add(sf);
    with sf do
    begin
      AStream.Read(Loc,SizeOf(TLocType));
      AStream.Read(Index,SizeOf(Integer));
      AStream.Read(Size,SizeOf(Integer));
      AStream.Read(Value,SizeOf(Integer));
    end;
 end;

 AStream.Read(LCount,SizeOf(Integer));
 for I:=0 to LCount-1 do
 begin
     NewFuncEntry;
     Fe :=Locals;
     AStream.Read(Fe.EntryTag,SizeOf(Integer));

 AStream.Read(cCount,SizeOf(Integer));
 for j:=0 to cCount-1 do
 begin
    sf :=TObjSymInfo.Create;
    Fe.Add(sf);
    with sf do
    begin
      AStream.Read(Loc,SizeOf(TLocType));
      AStream.Read(Index,SizeOf(Integer));
      AStream.Read(Size,SizeOf(Integer));
      AStream.Read(Value,SizeOf(Integer));
    end;
 end;

     AStream.Read(Ccount,SizeOf(Integer));
    // FuncsList.Add(Fe);
     for J:=0 to Ccount-1 do
     begin
        Mc := TByteRec.Create;
        Fe.CodeList.Add(Mc);
        AStream.Read(Mc.CodeMc,Sizeof(TCodeMc));
     end;
 end;

 AStream.Read(LCount,SizeOf(Integer));
 for I:=0 to LCount-1 do
 begin
    UnitInf :=TUnitInfo.Create;
    UnitsRefs.Add(UnitInf);
    with UnitInf do
    begin
      J:=Length(UnitInf.Name);
      AStream.Read(J,SizeOf(Integer));
      SetLength(UnitInf.Name,J);
      AStream.Read(Pointer(UnitInf.Name)^,J);
      AStream.Read(UnitInf.Version,SizeOf(Integer));
    end;
 end;
 //AStream.Read(cCount,SizeOf(Integer));
// StaticData.Size :=cCount;
 //AStream.Read(StaticData.Data^,cCount);
 AStream.Read(Version,SizeOf(Integer));
 lod :=true;
end;

procedure TBinObj.SaveToStream(AStream: TStream);
var
 I,J:integer;
 Mc:TByteRec;
 Fe:TFuncEntry;
 UnitInf:TUnitInfo;
begin
 AStream.Write(GlobalSymbs.Count,SizeOf(Integer));
 for I:=0 to  GlobalSymbs.Count-1 do
  with GlobalSymbs.GetObjSymInfo(I) do
  begin
    AStream.Write(Loc,SizeOf(TLocType));
    AStream.Write(Index,SizeOf(Integer));
    AStream.Write(Size,SizeOf(Integer));
    AStream.Write(Value,SizeOf(Integer));
  end;
  
 AStream.Write(FuncsList.Count,SizeOf(Integer));
 for I:= 0 to FuncsList.Count -1 do
 begin
    Fe :=TFuncEntry(FuncsList[I]);
    AStream.Write(Fe.EntryTag,SizeOf(Integer));

 AStream.Write(Fe.Count,SizeOf(Integer));
 for J:=0 to  Fe.Count-1 do
  with Fe.GetObjSymInfo(J) do
  begin
    AStream.Write(Loc,SizeOf(TLocType));
    AStream.Write(Index,SizeOf(Integer));
    AStream.Write(Size,SizeOf(Integer));
    AStream.Write(Value,SizeOf(Integer));
  end;

    AStream.Write(Fe.CodeList.Count,SizeOf(Integer));
    for J:= 0 to Fe.CodeList.Count-1 do
    begin
       Mc := Fe.GetByteRec(J);
       AStream.Write(Mc.CodeMc,Sizeof(TCodeMc));
    end;
 end;

 AStream.Write(UnitsRefs.Count,SizeOf(Integer));
 for I:= 0 to UnitsRefs.Count -1 do
 begin
    UnitInf :=TUnitInfo(UnitsRefs[I]);
    J:=Length(UnitInf.Name);
    AStream.Write(J,SizeOf(Integer));
    AStream.Write(Pointer(UnitInf.Name)^,Length(UnitInf.Name));
    AStream.Write(UnitInf.Version,SizeOf(Integer));
 end;

 //AStream.Write(StaticData.Size,SizeOf(Integer));
 //AStream.Write(StaticData.Data^,StaticData.Size);
 // AStream.Write(Version,SizeOf(Integer));
end;

end.
