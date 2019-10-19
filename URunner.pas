unit URunner;

interface
uses
  Windows, SysUtils, Classes,Utils,dialogs,UNodesBase,UCommon,UGenerator;
type
   EExecutionException=class(Exception);
   TRunner=class;
   EAbortRun=class(Exception);
   TPrintEvent=procedure (const txt:string)of object;
   TDbgEvent=procedure (ARunner:TRunner;const ALoc:TMcLoc) of object;
   PReg = ^TReg;
   TReg=packed record
     case integer of
       0:(vInt:integer);
       1:(UInt:Cardinal);
       2:(vflt:single);
       3:(vInt64:int64)
   end;
   TRunner=class
   private
      function GetReg(AReg:TRegDest):PReg;
      procedure CheckMem(APos,ALen:integer);
      function CalcAddr(const OPCode: TLoc): TMcLoc;
      function GetAddress(const AbRec: TMcLoc): TMcLoc;
      function Read(APos, ALen: integer): Int64Rec;
      procedure Write(const Src; APos, ALen: integer);
      procedure Sp_Inc(AValue:integer);
      procedure Push(Value:integer);
      function ReadLoc(const Loc: TLoc; ALen: integer): Int64Rec;
      procedure WriteLoc(const Loc: TLoc; ASrc: TRegDest; ALen: integer);
      function ReadfltLoc(const Loc: TLoc): single;
      procedure Print(ADsp: TDispType);
    procedure PushFrame;
    function VirtualCall: integer;
    function IntrfCall: integer;
    function NewObj:integer;
    function CastClass(AMustExists:boolean): integer;
    function CastInterface(AMustExists:boolean):integer;
    function Pop: integer;
    procedure PushErrVector(ANewHandler:integer);
    function PopErrVector():integer;
    procedure Execute(AIP:Integer);
    procedure HandlerScan();
    procedure ExitFinally;
    function ExecuteHandled(AIp: integer):boolean;
   public
      FMem:PByteArray;
      FSize:integer;
      Reg1:TReg;
      Reg2:TReg;
      Reg3:TReg;
      FieldTmp:TReg;
      F_cmp :boolean;
      FPc:integer;
      FBase:integer;
      FSp:integer;
      FDynMemPtr:integer;

      ErrVector:integer;
      ErrStatus:(esNoError,esError);
      ErrCode:integer;
      Code:array of TCodeMc;
      NotifyEvent:TDbgEvent;
      PrintEvent:TPrintEvent;
      destructor Destroy();override;
      procedure Clear();
      procedure Load(AStream:TStream);
      procedure Run();
      procedure ExportList(S:TStrings);
      function DynAlloc(ASize:integer):integer;
   end;

implementation
 
{ TRunner }
destructor TRunner.Destroy;
begin
  Clear;
  inherited;
end;

procedure TRunner.Clear;
begin
  Setlength(Code,0);
  FreeMem(FMem);
end;

procedure TRunner.Load(AStream: TStream);
var
 L,I:integer;
begin
   Clear;
   AStream.Read(L,4);
   FSize :=L+1024*1024;
   FDynMemPtr := FSize;
   GetMem(FMem,FSize);
   Fillchar(FMem[0],FSize,0);
   AStream.ReadBuffer(FMem[0],L);
   L := L + 4;
   FBase :=-1;
   FSp   := L;
   L :=(AStream.Size - AStream.Position)div SizeOf(TCodeMc);
   Setlength(Code,L);
   for I:= 0 to L -1 do
   begin
      AStream.Read(Code[I],Sizeof(TCodeMc));
   end;
end;

procedure TRunner.ExportList(S: TStrings);
var
 i:integer;
begin
   s.Clear;
   for I:= 0 to length(Code)-1 do
   begin
     S.Add(BcName( Code[I].Bytecode));
   end;
end;

procedure TRunner.CheckMem(APos,ALen: integer);
begin
    if (APos<0 )or(APos+ALen-1 >= fsize) then
       raise ECompException.Create('invalid mem pos '+inttostr(APos));
end;

function TRunner.Read(APos, ALen: integer):Int64Rec;
begin
  CheckMem(APos,ALen);
  Move(FMem[APos],Result,ALen);
end;

procedure TRunner.Write(const Src;APos,ALen: integer);
begin
  CheckMem(APos,ALen);
  Move(Src,FMem[APos],ALen);
end;

function TRunner.GetAddress(const AbRec: TMcLoc):TMcLoc;
begin
    Result := AbRec;
    case AbRec.LocType of
       vtLocal:begin
           Result.Addr:= FBase+Result.Addr ;
         end;
       vtFrame:begin
           Result.Addr:= FBase+Result.Addr -8;// 8 ret addr ,oldbase ,on stack
         end;
       vtStatic:begin

         end;
       vtCode:begin

         end;
    end;
end;

function TRunner.ReadfltLoc(const Loc:TLoc):single;
var
 v:TMcLoc;
begin
   v:=CalcAddr(Loc);
   CheckMem(v.Addr,4);
   Move(FMem[v.Addr],Result,4);
end;

function TRunner.ReadLoc(const Loc:TLoc; ALen: integer):Int64Rec;
var
 v:TMcLoc;
begin
   v:=CalcAddr(Loc);
   if v.LocType<> vtCode then
      Result := Read(v.Addr,ALen)
   else
      int64(Result) := v.Addr
end;

procedure TRunner.WriteLoc(const Loc:TLoc;ASrc:TRegDest; ALen: integer);
begin
   Write(GetReg(ASrc)^,CalcAddr(Loc).Addr,ALen);
end;

procedure TRunner.Sp_Inc(AValue: integer);
begin
  FSp := FSp + AValue;
  if FSp<0 then
     raise ECompException.Create('stack underflow ');
  if FSp >= FSize then
     raise ECompException.Create('stack overflow ');
end;

function TRunner.CalcAddr(const OPCode:TLoc):TMcLoc;
var
 t:integer;
begin
    case OPCode.kind of
       vtOffset,vtpOffset:begin  //
            Result := GetAddress(OPCode.Base);
            if OPCode.kind = vtpOffset then
                Result.Addr :=Read(Result.Addr,4).Lo;
            if OPCode.Idx.LocType=vtLiteral then
               t :=OPCode.Idx.Addr
            else
               t :=integer(Read(GetAddress(OPCode.Idx).Addr,4).Lo);
            Result.Addr := Result.Addr +t;
         end;
       vtPtr:begin
            Result := GetAddress(OPCode.Base);
            Result.Addr :=Read(Result.Addr,4).Lo;
         end;
       else
         Result := GetAddress(OPCode.Base);
    end;
end;

function TRunner.GetReg(AReg: TRegDest): PReg;
begin
    case AReg of
      rgReg1:Result :=@Reg1;
      rgReg2:Result :=@Reg2;
      rgReg3:Result :=@Reg3;
    else
      Result :=nil;
    end;
end;

function TRunner.CastClass(AMustExists:boolean):integer;
var
  vType:integer;
begin
   Result := Reg1.vInt;
   vType := Result;
   while vType <> 0 do
   begin
        vType := Read(vType ,4).Lo;
        if vType = Reg2.vInt then
           Exit;
        vType := Read(vType-12,4).Lo; // get parent class
   end;
   if AMustExists then
      raise ECompException.Create('object not supported');
   Result := 0;
end;

function TRunner.CastInterface(AMustExists:boolean):integer;
var
  V,I,IOffset,IID,vType:integer;
  IntfCount:integer;
begin
   vType := Reg1.vInt;
   while vType <> 0 do
   begin
       vType := Read(vType,4).Lo;// obj vtable ptr
       V := Read(vType-8,4).Lo; // interfaces tables
       V := Read(V,4).Lo;    //deref
       IntfCount := Read(V+0,4).Lo;
       inc(V,4);
       for I := 0 to IntfCount-1 do
       begin
          IID := Read(V+4,4).Lo;
          if IID = Reg2.vInt then
          begin
             IOffset:= Read(V+8,4).Lo;
             Result := Reg1.vInt + IOffset;
             Exit;
          end;
          V := V + 12; {iTable+IID+IOffset}
       end;
       vType := Read(vType-12,4).Lo; // get parent class
   end;
   if AMustExists then
      raise ECompException.Create('interface not supported');
   Result := 0;
end;

function TRunner.VirtualCall():integer;
var
  Entry:integer;
begin
    Entry  := Reg1.vInt;
    if Reg3.vInt=0 then   //not a Classmethod
       Entry  := Read(Entry,4).Lo;
    Result := Read(Entry+Reg2.vInt*SIZEOFPOINTER,4).Lo;
end;

function TRunner.IntrfCall():integer;
const SelfParam=16;{self+retaddr+pc+base}
var
  Entry,IOffset:integer;
begin
    Entry  := Read(Reg1.vInt,4).Lo;
    IOffset := Read(Entry+8,4).Lo;
    // update self
    FMem[FBase-SelfParam]:=  FMem[FBase-SelfParam]-IOffset;
    Entry := Read(Entry,4).Lo; // load funcs table
    Result := Read(Entry+Reg2.vInt*SIZEOFPOINTER,4).Lo;
end;

procedure TRunner.Print(ADsp:TDispType);
const BOOL_STR:array[boolean]of string=('False','True');
var
  S,V:string;
  I:integer;
  C:Char;
begin
    if not Assigned(PrintEvent) then
       Exit;
    case ADsp of
         ds_Int: S :=IntToStr(Reg1.vInt);
        ds_UInt: S :=IntToStr(Reg1.UInt);
        ds_Char: S :=Chr(Reg1.vInt);
         ds_Ptr: S :=IntToHex(Reg1.vInt,8);
       ds_Float: S :=FloatToStr(Reg1.vflt);
        ds_Bool: S :=BOOL_STR[Reg1.vInt <> 0];
   ds_CharArray: begin
              if Reg2.vInt= 0 then  // open string
                 Reg2.vInt:= high(Short);
              for I:= Reg1.vInt to Reg1.vInt+Short(Reg2.vInt)-1 do
              begin
                 C:=Chr(FMem[I]);
                 if C=#0 then
                    break;
                 S:=S+C;
              end;
         end;
    else
       S:='';
    end;
    V:='';
    PrintEvent(s);
end;

function TRunner.DynAlloc(ASize: integer): integer;
begin
  FDynMemPtr := FDynMemPtr - ASize;
  if FDynMemPtr <= FSp then
     raise ECompException.Create('mem alloc error');
  Result := FDynMemPtr;
end;

function TRunner.NewObj():integer;
var
  Sz,V,I,IOffset,iTable,vType:integer;
  IntfCount:integer;
begin
   Sz  := Read(Reg1.vInt-4,4).Lo;//instance size
   Result := DynAlloc(Sz);
   Write(Reg1.vInt,Result,4); // fill vTable ptr
   vType :=Reg1.vInt;
   repeat // init interfaces tables
       V := Read(vType-8,4).Lo;
       V := Read(V,4).Lo;    //deref
       IntfCount := Read(V+0,4).Lo;
       inc(V,4);
       for I := 0 to IntfCount-1 do
       begin
          iTable  := V;
          IOffset := Read(V+8,4).Lo;
          Write(iTable,Result+IOffset,4);
          V := V + 12; {iTable+IID+IOffset}
       end;
       vType := Read(vType-12,4).Lo; //  get parent class
       if vType= 0 then
          break;
       vType := Read(vType,4).Lo; //deref
   until False;
end;

procedure TRunner.PushFrame();
begin
    Push(FPc);
    Push(FBase);
    FBase := FSp;
end;

procedure TRunner.Push(Value: integer);
begin
    Write(Value,FSp,4);
    Sp_Inc(4);
end;

function TRunner.Pop(): integer;
begin
   Sp_Inc(-4);
   Result:= Read(FSp,4).Lo;
end;

procedure TRunner.PushErrVector(ANewHandler:integer);
begin
    Push(ANewHandler);// handler proc addr
    Push(FBase);
    Push(ErrVector);
    ErrVector := FSp;
end;

function TRunner.PopErrVector():integer;
begin
    FSp := ErrVector;
    ErrVector := Pop();
    FBase  := Pop();
    Result := Pop();
end;

function TRunner.ExecuteHandled(AIp:integer):boolean;
begin
   Result := False;
   try
      Execute(AIp);
      Result := True;                             ;
   except
      on e:EAbortRun do raise;// exit;
      on e:Exception do
      begin
          ErrCode := e.HelpContext;
          ErrStatus := esError;
      end;
   end;
end;

procedure TRunner.HandlerScan();
var
   Handler:integer;
begin
   Handler:=0;
   try// test error vector stack
      Handler := PopErrVector();                                ;
   except
   end;
   if Handler <> 0 then
      ExecuteHandled(Handler);
   if ErrStatus<>esNoError then // unhandled exception
      raise ECompException.CreateHelp(Inttostr(ErrCode),ErrCode);
end;

procedure TRunner.ExitFinally();
var
 o:integer;
begin
   o:= FPc;
   HandlerScan();
   FPc := o;
end;

procedure TRunner.Execute(AIP:Integer);
begin
  FPc := AIP;
  repeat
      if (FPc< 0) or(FPc>= length(Code)) then
         raise ECompException.Create('error FPc pos '+inttostr(FPc));
      with Code[FPc]do
        case Bytecode of
           bcLoad_i8:GetReg(vReg).vInt := Shortint(ReadLoc(Loc,1).Bytes[0]);
           bcLoad_u8:GetReg(vReg).UInt := Byte(ReadLoc(Loc,1).Bytes[0]);
          bcLoad_i16:GetReg(vReg).vInt := Smallint(ReadLoc(Loc,2).Words[0]);
          bcLoad_u16:GetReg(vReg).UInt := Word(ReadLoc(Loc,2).Words[0]);
          bcLoad_i32:GetReg(vReg).vInt := integer(ReadLoc(Loc,4).Lo);
          bcLoad_u32:GetReg(vReg).UInt := Cardinal(ReadLoc(Loc,4).Lo);
          bcLoad_flt:GetReg(vReg).vflt := ReadfltLoc(Loc);
           bcLoad_64:GetReg(vReg).vInt64 :=int64( ReadLoc(Loc,8));

          bcSave_i8: WriteLoc(Loc,vReg,1);
          bcSave_u8: WriteLoc(Loc,vReg,1);
          bcSave_i16:WriteLoc(Loc,vReg,2);
          bcSave_u16:WriteLoc(Loc,vReg,2);
          bcSave_i32:WriteLoc(Loc,vReg,4);
          bcSave_u32:WriteLoc(Loc,vReg,4);
          bcSave_flt:WriteLoc(Loc,vReg,4);
           bcSave_64:WriteLoc(Loc,vReg,8);

         bcLoadlabel:GetReg(vReg).vInt := OprdInt;
           bcLiteral:GetReg(vReg).vflt := Oprdflt;
        bcflt_To_Int:GetReg(vReg).vInt :=Trunc(GetReg(vReg).vflt);
        bcInt_To_flt:GetReg(vReg).vflt :=GetReg(vReg).vInt;
           bcPrint:begin
                Print(TDispType(OprdInt));
             end;
          bcRegToTmp:FieldTmp :=GetReg(vReg)^;
           bcBitsRead:begin
                 with LongRec(OprdInt) do
                 begin
                   GetReg(vReg).UInt :=(GetReg(vReg).UInt and Hi)shr Lo;
                 end;
             end;
          bcBitsWrite:begin
                 with LongRec(OprdInt) do
                 begin
                   GetReg(vReg).UInt:=  GetReg(vReg).UInt and Hi;
                   GetReg(vReg).UInt := GetReg(vReg).UInt or (FieldTmp.UInt shl Lo);
                 end;
             end;
           bcParam:begin
                Write(GetReg(vReg).vInt,FSp,OprdInt);
                Sp_Inc(OprdInt);
             end;
           bcResultAddr:begin
                Write(GetReg(vReg).vInt,FSp,OprdInt);
                Sp_Inc(OprdInt);
             end;
           bcFunEnter:begin
                Sp_Inc(OprdInt);
             end;
          bcCall:begin
                PushFrame();
                Execute(Reg1.vInt );
                continue;;
             end;
          bcvCall:begin
                PushFrame();
                Execute(VirtualCall());
                continue;
             end;
          bciCall:begin
                PushFrame();
                Execute(IntrfCall());
                continue;
             end;
           bcRet:begin
                FSp := FBase;// pop frame
                FBase:=Pop();
                FPc  :=Pop()+1;
                Sp_Inc(OprdInt);
                break;
             end;
            bcJump:begin
               FPc :=OprdInt;
               continue;
             end;
            bcCondJump:begin
               if F_cmp then
                  FPc :=Reg1.vInt
               else
                  FPc :=Reg2.vInt;
               continue;
             end;

              bciAdd:Reg3.vInt := Reg1.vInt + Reg2.vInt;
              bciSub:Reg3.vInt := Reg1.vInt - Reg2.vInt;
              bciMul:Reg3.vInt := Reg1.vInt * Reg2.vInt;
              bciModulo:Reg3.vInt := Reg1.vInt mod Reg2.vInt;
              bciDiv:Reg3.vInt := Reg1.vInt div Reg2.vInt;

              bcAdd:Reg3.UInt := Reg1.UInt + Reg2.UInt;
              bcSub:Reg3.UInt := Reg1.UInt - Reg2.UInt;
              bcMul:Reg3.UInt := Reg1.UInt * Reg2.UInt;
              bcModulo:Reg3.UInt := Reg1.UInt mod Reg2.UInt;
              bcDiv:Reg3.UInt := Reg1.UInt div Reg2.UInt;

               bcOr:Reg3.UInt := Reg1.UInt or Reg2.UInt;
              bcAnd:Reg3.UInt := Reg1.UInt and Reg2.UInt;
              bcXor:Reg3.UInt := Reg1.UInt xor Reg2.UInt;
              bcShl:Reg3.UInt := Reg1.UInt shl Reg2.UInt;
              bcShr:Reg3.UInt := Reg1.UInt shr Reg2.UInt;

              bcfAdd:Reg3.vflt := Reg1.vflt + Reg2.vflt;
              bcfSub:Reg3.vflt := Reg1.vflt - Reg2.vflt;
              bcfMul:Reg3.vflt := Reg1.vflt * Reg2.vflt;
              bcfDiv:Reg3.vflt := Reg1.vflt / Reg2.vflt;
            bcfMinus:Reg3.vflt := -Reg1.vflt;

              bcMinus:Reg3.vInt := -Reg1.vInt;
               bcComp:Reg3.vInt := not Reg1.vInt;
               bcAddr:GetReg(vReg).vInt := CalcAddr(Loc).Addr;

                 bc_z:F_cmp := Reg1.vInt <> 0;
                bcEqu:F_cmp := Reg1.vInt = Reg2.vInt;
              bciLess:F_cmp := Reg1.vInt < Reg2.vInt;
                bciGr:F_cmp := Reg1.vInt > Reg2.vInt;
             bcNotequ:F_cmp := Reg1.vInt <> Reg2.vInt;
           bciLessEqu:F_cmp := Reg1.vInt <= Reg2.vInt;
             bciGrEqu:F_cmp := Reg1.vInt >= Reg2.vInt;

               bcLess:F_cmp := Reg1.UInt < Reg2.UInt;
                 bcGr:F_cmp := Reg1.UInt > Reg2.UInt;
            bcLessEqu:F_cmp := Reg1.UInt <= Reg2.UInt;
              bcGrEqu:F_cmp := Reg1.UInt >= Reg2.UInt;

               bcfEqu:F_cmp := Reg1.vflt = Reg2.vflt;
              bcfLess:F_cmp := Reg1.vflt < Reg2.vflt;
                bcfGr:F_cmp := Reg1.vflt > Reg2.vflt;
            bcfNotequ:F_cmp := Reg1.vflt <> Reg2.vflt;
           bcfLessEqu:F_cmp := Reg1.vflt <= Reg2.vflt;
             bcfGrEqu:F_cmp := Reg1.vflt >= Reg2.vflt;

            bc_Is_Cls:F_cmp := CastClass(False)<>0;
          bc_Is_Intrf:F_cmp := CastInterface(False)<>0;

             bcGetCls:Reg3.vInt := CastClass(True);
           bcGetIntrf:Reg3.vInt := CastInterface(True);
        bcConstructor:Reg1.vInt := NewObj();
         bcRaiseError:raise ECompException.CreateHelp(Inttostr(Reg1.vInt),Reg1.vInt);
            bcReRaise:raise ECompException.CreateHelp(Inttostr(ErrCode),ErrCode);
    bcEnterHandler:begin
                       Push(ErrCode);// used to trace error poped in ExitHandler | PopErrCode
                       PushErrVector(OprdInt);
                       if not ExecuteHandled(FPC+1)then
                       begin
                          HandlerScan();
                          Inc(FPc);
                       end;
                       continue;
                  end;
     bcHandlerRet:begin//exex  with finally or unhandled exception
                  break;
               end;
     bcExitHandler:begin // no error "normal"
                  if ErrVector=0 then
                     break;
                  if OprdInt <> 0 then
                     ExitFinally() //pop and execute handler :try..finally
                  else
                     PopErrVector();//pop handler try..catch
                  Inc(FPc);
                  Pop();// error code pushed at TryEnter
                  break;
               end;
     bcClearErr:begin
                 ErrStatus := esNoError;
                 break;
               end;
     bcPopErrCode:begin // when err was handled
      //gets the initial code err before the handler this value may be used after
      // the handler for "reThrow"
                 ErrCode :=Pop();
               end;
     bcReadErr:Reg1.vInt:= ErrCode;
     bcLineNumber:begin
                 if Assigned(NotifyEvent) then
                    NotifyEvent(Self,Loc.Base);
              end;
      bcHalt:break;
        else
            raise ECompException.Create('opcode unknown '+inttostr(ord(Bytecode)));
        end;
     inc(FPc);
  until False;
end;

procedure TRunner.Run;
begin
  try
   Execute(0);
  except
     on e:EAbortRun do;
     else
        raise;
  end;
end;



end.
