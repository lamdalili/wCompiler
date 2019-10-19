unit Unit1;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, StdCtrls,USymbolesTable, ExtCtrls, ComCtrls,
  ULexParser,math,USynParser,UNodesBase,UPreProcessor,UCompiler, ActnList,
  Menus,URunner, ToolWin, ImgList, SynEditHighlighter,
  SynHighlighterCpp, SynEdit,USynEditEx,UGenerator, XPMan;
type
  TDebuggerState = (dsStopped, dsRunning, dsPaused);
  TDebugger = class(TForm)
    Splitter1: TSplitter;
    Panel1: TPanel;
    StatusBar1: TStatusBar;
    Panel2: TPanel;
    ListBox1: TListBox;
    Splitter2: TSplitter;
    Panel3: TPanel;
    BCompile: TButton;
    IRLIst: TListBox;
    imglActions: TImageList;
    actlMain: TActionList;
    actDebugRun: TAction;
    actDebugStep: TAction;
    actDebugStepIn: TAction;
    actDebugStop: TAction;
    actClearAllBreakpoints: TAction;
    tbDebug: TToolBar;
    tbtnRun: TToolButton;
    tbtnStep: TToolButton;
    tbtnStepIn: TToolButton;
    tbtnStop: TToolButton;
    tbtnBreksPointClear: TToolButton;
    ToolButton1: TToolButton;
    PageControl1: TPageControl;
    App: TTabSheet;
    Box2: TListBox;
    TabSheet2: TTabSheet;
    Splitter3: TSplitter;
    TabSheet3: TTabSheet;
    Splitter30: TSplitter;
    TabSheet4: TTabSheet;
    Splitter31: TSplitter;
    TabSheet5: TTabSheet;
    Splitter5: TSplitter;
    SynEdit1: TSynEdit;
    SynCppSyn1: TSynCppSyn;
    SynEdit2: TSynEdit;
    SynEdit3: TSynEdit;
    SynEdit4: TSynEdit;
    SynEdit5: TSynEdit;
    XPManifest1: TXPManifest;
    procedure BCompileClick(Sender: TObject);
    procedure ListBox1DblClick(Sender: TObject);
    procedure Splitter2Moved(Sender: TObject);
    procedure FormCreate(Sender: TObject);
    procedure IRLIstDrawItem(Control: TWinControl; Index: Integer;
      Rect: TRect; State: TOwnerDrawState);
    procedure actDebugRunExecute(Sender: TObject);
    procedure actDebugStepExecute(Sender: TObject);
    procedure actDebugStepInExecute(Sender: TObject);
    procedure actDebugStopExecute(Sender: TObject);
    procedure actClearAllBreakpointsExecute(Sender: TObject);
    procedure SynEdit1StatusChange(Sender: TObject;
      Changes: TSynStatusChanges);
    procedure Button1Click(Sender: TObject);
  private
    FState:TDebuggerState;
    MoveStep:(spNone,spStepIn,spStepOver);
    Ticks:cardinal;
    StrBuff:string;
    Compiler:TMainComp;
    _NextInstrc:TMcLoc;
    FCompiled:boolean;
    function LoadStrCode(const AStr: string;AComp:TComp): string;
    procedure ClearMsgsList;
    procedure dbgHandler(ARunner:TRunner;const ALoc:TMcLoc);
    procedure SaveStrCode(const AStr, CompiledTxt: string);
    procedure dbgPrint(const Msg: string);
    procedure SetState(const Value: TDebuggerState);
    procedure Showdbgtxt;
  public
    property State:TDebuggerState read FState write SetState;
  end;

var
  Debugger: TDebugger;

implementation
{$R *.dfm}
uses UTypes,Utils,UIRGen;

var
 DefHeight:integer;
function TDebugger.LoadStrCode(const AStr:string;AComp:TComp):string;
begin

  if SameText(AStr,'u1') then
  begin
     Result :=SynEdit2.Lines.Text;
     AComp.Data :=SynEdit2;
  end else if SameText(AStr,'u2') then
  begin
     Result :=SynEdit3.Lines.Text;
     AComp.Data :=SynEdit3;
  end else if SameText(AStr,'u3') then
  begin
     Result :=SynEdit4.Lines.Text;
     AComp.Data :=SynEdit4;
  end else if SameText(AStr,'System') then
  begin
     Result :=SynEdit5.Lines.Text;
     AComp.Data :=SynEdit5;
  end else
      raise ECompException.Create('invalid unit '+AStr);
end;

procedure TDebugger.SaveStrCode(const AStr,CompiledTxt:string);
begin

end;

procedure TDebugger.ListBox1DblClick(Sender: TObject);
var
 err:TMsgRec;
 Tab:TTabSheet;
 SynEdit:TSynEdit;
begin
   if ListBox1.ItemIndex = -1 then
      Exit;
   err:=TMsgRec(ListBox1.Items.Objects[ListBox1.ItemIndex]);
   SynEdit := TSynEdit(err.sData);
   Tab := TTabSheet(SynEdit.Parent);
   PageControl1.ActivePage := Tab;
   SynEdit.GotoLineAndCenter(err.sLine+1);
   SynEdit.SetFocus ;
   ListBox1.ItemIndex := -1;
end;

procedure TDebugger.ClearMsgsList();
var
 i:integer;
begin
 for I:= 0 to ListBox1.Items.Count-1 do
     ListBox1.Items.Objects[I].Free;

 ListBox1.Clear;
end;


procedure TDebugger.dbgHandler(ARunner:TRunner;const ALoc:TMcLoc);
    function  IsStopPos():boolean;
    begin
       Result := (_NextInstrc.Unitidx=ALoc.Unitidx)and (_NextInstrc.Addr=ALoc.Addr);
       if Result then
          _NextInstrc.Unitidx := -2;
    end;
var
 t:cardinal;
 Editor:TSynEdit;
 Lf:TSynLineInf;
 I:integer;
begin
//
  if ALoc.Unitidx=-1 then
     Editor:= SynEdit1
  else
     Editor:=TSynEdit(Compiler.Comps(ALoc.Unitidx).Data);
  //
  if (MoveStep=spStepIn) or IsStopPos()or (Inf_breakPoint in Editor.GetlineInf(ALoc.Addr)) then
  begin
      PageControl1.ActivePage :=  TTabSheet(Editor.Parent);
      Editor.CurrentLine :=ALoc.Addr+1;
      State := dsPaused;
      MoveStep :=spNone;
      repeat
         Sleep(20);
         Application.ProcessMessages;
      until State <> dsPaused;
      if MoveStep=spStepOver then
      begin
           Lf := Editor.GetlineInf(ALoc.Addr);
           if Inf_CallLine in Lf then
           begin
             _NextInstrc.Unitidx := ALoc.Unitidx;
             _NextInstrc.Addr := -1;
             for I:= ALoc.Addr+1 to Editor.Lines.Count-1 do
              if Inf_ExecLine in Editor.GetlineInf(I) then
              begin
                 _NextInstrc.Addr:=I;
                 break;
              end;
             if _NextInstrc.Addr=-1 then
                 MoveStep:=spStepIn;
           end else
                  MoveStep:=spStepIn;
      end;
  end;
  t :=GetTickCount();
  if (t-Ticks)>100 then
  begin
     Application.ProcessMessages;
     Ticks :=t;
     if State=dsStopped then
        raise EAbortRun.Create('');
  end; 
end;


procedure TDebugger.dbgPrint(const Msg:string);
begin
   StrBuff := StrBuff + Msg;
end;

procedure TDebugger.Showdbgtxt();
var
 Memo:TMemo;
 frm:TForm;
begin
   frm :=TForm.Create(nil);
   Memo:=TMemo.Create(frm);
   try
     Memo.Parent :=frm;
     Memo.Font := Debugger.Font;
     Memo.Font.Size := 20;
     Memo.Align :=alClient;
     Memo.Text :=StrBuff;
     Memo.ReadOnly :=True;
     frm.Position :=poDesktopCenter;
     frm.ShowModal();
   finally
     frm.Free;
   end;
end;

procedure TDebugger.BCompileClick(Sender: TObject);
var
 i:integer;
begin
 if Assigned(Compiler) then
    FreeAndNil(Compiler);
 randseed :=234234124;
 symidx := 0;
 IRLIst.Clear();
 Compiler:=TMainComp.Create('App');
 ClearMsgsList();
 _NextInstrc.Unitidx:=-2;
 FCompiled:=False;
 try
     Compiler.Data :=SynEdit1;
     Compiler.LoadUnitCode :=LoadStrCode;
     Compiler.SaveUnitCode :=SaveStrCode;
     Compiler.Parse(SynEdit1.Lines.Text);
     Compiler.StartDecls(IRLIst.Items);
     Compiler.GetNextTokenAndCheck(uuNone);
     FCompiled:= Compiler.Build();
 except
      on e:ECompException do
        Compiler.Msg_Report(msError,e.Message,0);
 end;
 for I:= 0 to Compiler._CompList.Count-1 do
     Compiler.Comps(I).ExportMsgs(ListBox1.Items);
 if Compiler._CompList.Count =0 then
    Compiler.ExportMsgs(ListBox1.Items);
 if ListBox1.Items.Count<>0  then
    ListBox1.Height:=DefHeight
 else
    ListBox1.Height:=0;
 if not FCompiled then
 begin
   Compiler.Free;
   Compiler :=nil;
 end;
 caption :=inttostr(symidx);
end;

procedure TDebugger.Splitter2Moved(Sender: TObject);
begin
  DefHeight:= ListBox1.Height;
end;

procedure TDebugger.FormCreate(Sender: TObject);
begin
  DefHeight := ListBox1.Height;
  ListBox1.Height := 0;
end;

procedure TDebugger.IRLIstDrawItem(Control: TWinControl; Index: Integer;
  Rect: TRect; State: TOwnerDrawState);
const COLORARR:array[0..1]of TColor=(clAqua,clCream);
begin
  IRLIst.Canvas.Brush.Color:=COLORARR[integer(IRLIst.Items.Objects[index ])];
  IRLIst.Canvas.FillRect(Rect);
  with Rect do
     IRLIst.Canvas.TextOut(Left,Top, IRLIst.Items[index]);
end;

procedure TDebugger.SetState(const Value: TDebuggerState);
begin
  actDebugStop.Enabled := Value in [dsRunning, dsPaused];
  actDebugRun.Enabled  := Value in [dsStopped, dsPaused];
  actDebugStep.Enabled := Value in [dsPaused];
  actDebugStepIn.Enabled := actDebugStep.Enabled;

  FState := Value;
end;

procedure TDebugger.actDebugRunExecute(Sender: TObject);
var
 i:integer;
 Runner:TRunner;
begin
   if not FCompiled  then
      BCompileClick(nil)
   else for I:= 0 to Compiler._CompList.Count-1 do
       if Compiler.Comps(I).UnitChanged then
       begin
          BCompileClick(nil);// recompile
          break;
       end;
   if not FCompiled  then
      Exit;
   MoveStep:=spNone;
   _NextInstrc.Unitidx:=-2;
   if State = dsPaused then
   begin
     State := dsRunning;
     Exit;
   end;
   State := dsRunning;
   for I:= 0 to Compiler._CompList.Count-1 do
       TSynEdit(Compiler.Comps(I).Data).Running:=True;
   Runner:=TRunner.Create;
   try
      StrBuff:='';
      Runner.NotifyEvent := dbgHandler;
      Runner.PrintEvent := dbgPrint;
      Compiler.OutputStream.Position := 0;
      Runner.Load(Compiler.OutputStream);
      Runner.ExportList( Box2.Items);
      Runner.Run();
      Showdbgtxt();
   finally
      Runner.Free;
      State := dsStopped;
      for I:= 0 to Compiler._CompList.Count-1 do
          TSynEdit(Compiler.Comps(I).Data).Running:=False;
   end;
end;

procedure TDebugger.actDebugStepExecute(Sender: TObject);
begin
   State := dsRunning;
   MoveStep:=spStepOver;
end;

procedure TDebugger.actDebugStepInExecute(Sender: TObject);
begin
   State := dsRunning;
   MoveStep:=spStepIn;
end;

procedure TDebugger.actDebugStopExecute(Sender: TObject);
begin
   State:=dsStopped;
end;

procedure TDebugger.actClearAllBreakpointsExecute(Sender: TObject);
var
 i,J:integer;
begin
  if not Assigned(Compiler) then
     Exit;
  for I:= 0 to Compiler._CompList.Count-1 do
    with TSynEdit(Compiler.Comps(I).Data) do
    begin
       for J:= 0 to Lines.Count-1 do
           ResetLineProps(J,[Inf_BreakPoint]);
       Invalidate;
    end;
end;


procedure TDebugger.SynEdit1StatusChange(Sender: TObject;
  Changes: TSynStatusChanges);
var
  p: TBufferCoord;
begin
  if Changes * [scAll, scCaretX, scCaretY] <> [] then
  begin
    p := TSynEdit(Sender).CaretXY;
    Statusbar1.Panels[0].Text := Format('%6d :%3d', [p.Line, p.Char]);
  end;
end;

procedure TDebugger.Button1Click(Sender: TObject);
begin
  try
      raise EAbstractError.Create('jkjk');
  except
        
        try
          tag:=tag div tag;
        except
           raise;
        end;

        raise;

  end;
end;

end.



