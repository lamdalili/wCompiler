unit USynEditEx;
interface

uses
  Windows, Messages, SysUtils, Classes, Graphics, Controls, Forms, Dialogs,
  ActnList, ImgList, ComCtrls, ToolWin, SynEdit, SynEditHighlighter,
  SynHighlighterPas, Menus, SynEditTypes,SynEditMiscClasses,
  StdCtrls;

type
  TDebugSupportPlugin = class(TSynEditPlugin)
  protected
    procedure AfterPaint(ACanvas: TCanvas; const AClip: TRect;
              FirstLine, LastLine: integer); override;
    procedure LinesInserted(FirstLine, Count: integer); override;
    procedure LinesDeleted(FirstLine, Count: integer); override;
  end;
  TSynLineInf=set of (Inf_None,Inf_BreakPoint,inf_ExecLine,Inf_CallLine);

  TSynEdit=class(SynEdit.TSynEdit)
  private
    procedure SetCompiled(const Value: boolean);
    procedure SetCurrentLine(ALine: integer);
    procedure SetRunning(const Value: boolean);
  protected
    FCompiled:boolean;
    FRunning  :boolean;
    FCurrentLine:integer;
    FTextVersion:integer;
    procedure DoChange;override;
    procedure DoOnGutterClick(Button: TMouseButton; X, Y: integer); override;
    function DoOnSpecialLineColors(Line: integer;
             var Foreground, Background: TColor): boolean;override;
  public
    procedure ClearLinesInfos;
    constructor Create(AOwner: TComponent); override;
    function GetlineInf(ALine:integer):TSynLineInf;
    procedure SetLineProps(ALine:integer;AInf:TSynLineInf);
    procedure ResetLineProps(ALine:integer;AInf:TSynLineInf);
    property Compiled:boolean read FCompiled write SetCompiled;
    property Running:boolean read FRunning write SetRunning;
    property CurrentLine:integer read FCurrentLine write SetCurrentLine;
    property TextVersion:integer read FTextVersion;
  end;

implementation
uses UGlyphsDbg;

{ TGutterMarkDrawPlugin }

procedure TDebugSupportPlugin.AfterPaint(ACanvas: TCanvas; const AClip: TRect;
  FirstLine, LastLine: integer);
var
  LH, X, Y, CL: integer;
  ImgIndex: integer;
  Glyphs:TImageList;
  Linf:TSynLineInf;
begin
    Glyphs := UGlyphsDbg.DataModule1.imglGutterGlyphs;
    FirstLine := Editor.RowToLine(FirstLine);
    LastLine  := Editor.RowToLine(LastLine);
    X := 14;
    LH := Editor.LineHeight;
    while FirstLine <= LastLine do
    begin
      Y := (LH - Glyphs.Height) div 2
           + LH * (Editor.LineToRow(FirstLine) - Editor.TopLine);
      CL := TSynEdit(Editor).CurrentLine;
      Linf :=TSynEdit(Editor).GetLineInf(FirstLine-1);
     with TSynEdit(Editor) do
      if Running and(CL = FirstLine)  then
      begin
          ImgIndex := 1;
      end else if not Compiled then
      begin
        if Inf_BreakPoint in Linf then
           ImgIndex := 6
        else
           ImgIndex := -1;
      end else if Inf_ExecLine in Linf then
      begin
        if Inf_BreakPoint in Linf then
          ImgIndex := 3
        else
          ImgIndex := 0;
      end else begin
        if Inf_BreakPoint in Linf then
          ImgIndex := 4
        else
          ImgIndex := -1;
      end;
      if ImgIndex >= 0 then
         Glyphs.Draw(ACanvas, X, Y, ImgIndex);
      Inc(FirstLine);
    end;
end;

procedure TDebugSupportPlugin.LinesInserted(FirstLine, Count: integer);
begin
// Note: You will need this event if you want to track the changes to
//       breakpoints in "Real World" apps, where the editor is not read-only
end;

procedure TDebugSupportPlugin.LinesDeleted(FirstLine, Count: integer);
begin
// Note: You will need this event if you want to track the changes to
//       breakpoints in "Real World" apps, where the editor is not read-only
end;

{ TSynEdit }

constructor TSynEdit.Create(AOwner: TComponent);
begin
  inherited;
  TDebugSupportPlugin.Create(Self);
  FCurrentLine :=-1;
end;

procedure TSynEdit.DoChange;
begin
  inherited;
  FCurrentLine :=-1;
  inc(FTextVersion);
end;

procedure TSynEdit.DoOnGutterClick(Button: TMouseButton; X, Y: integer);
var
 Line:integer;
 C:TSynLineInf;
begin
  inherited;
  Line := DisplayToBufferPos(PixelsToRowColumn(X,Y)).Line;
  Line:= RowToLine(Line)-1;
  C:= GetLineInf(Line);
  if Inf_BreakPoint in C then
     ResetLineProps(Line,[Inf_BreakPoint])
  else
     SetLineProps(Line,[Inf_BreakPoint]);
  Invalidate();
end;

function TSynEdit.DoOnSpecialLineColors(Line: integer; var Foreground,
  Background: TColor): boolean;
var
  Linf:TSynLineInf;
begin
    Linf := GetLineInf(Line-1);
    Result :=False;
    if CurrentLine=Line then
    begin
      Result := TRUE;
      Foreground := clWhite;
      Background := clBlue;
    end else if Inf_BreakPoint in Linf then
    begin
      Result := TRUE;
      Foreground := clWhite;
      if Running  and not (Inf_ExecLine in Linf) then
        Background := clGray
      else
        Background := clRed;
    end;
 // Result:= inherited DoOnSpecialLineColors(Line,Foreground,Background);
end;

function TSynEdit.GetLineInf(ALine: integer): TSynLineInf;
begin
 if (ALine >=0)and(ALine<Lines.Count)then
    Result := TSynLineInf(byte(Lines.Objects[ALine]))
 else
    byte(Result):=0;//replace
end;


procedure TSynEdit.SetLineProps(ALine: integer;AInf:TSynLineInf);
var
 V:TSynLineInf;
begin
  if (ALine >=0)and(ALine<Lines.Count)then
  begin
     V:= GetLineInf(ALine);
     V := V + AInf;
     Lines.Objects[ALine]:=Pointer(byte(V));
  end;
end;

procedure TSynEdit.SetCompiled(const Value: boolean);
begin
  FCompiled := Value;
  FCurrentLine :=-1;
//  ReadOnly :=FDebugging;
  Invalidate;
end;

procedure TSynEdit.ResetLineProps(ALine: integer;AInf:TSynLineInf);
var
 V:TSynLineInf;
begin
  if (ALine >=0)and(ALine<Lines.Count)then
  begin
     V:= GetLineInf(ALine);
     V :=V - AInf;
     Lines.Objects[ALine]:=Pointer(byte(V));
  end;
end;

procedure TSynEdit.SetCurrentLine(ALine: integer);
begin
  if FCurrentLine <> ALine then
  begin
    InvalidateGutterLine(FCurrentLine);
    InvalidateLine(FCurrentLine);
    FCurrentLine := ALine;
    if (FCurrentLine >= 0) and (CaretY <> FCurrentLine) then
      CaretXY := BufferCoord(1, FCurrentLine);
    InvalidateGutterLine(FCurrentLine);
    InvalidateLine(FCurrentLine);
  end;
end;

procedure TSynEdit.ClearLinesInfos;
var
  I:integer;
begin
   for I:=0 to Lines.Count-1 do
      ResetLineProps(I,[Inf_ExecLine]);
   Invalidate;
end;

procedure TSynEdit.SetRunning(const Value: boolean);
begin
  FRunning := Value;
  FCurrentLine :=-1;
  ReadOnly :=  FRunning;
  Invalidate;
  FRunning := Value;
end;
 
end.
