program Project2;

uses
  Forms,
  Unit1 in 'Unit1.pas' {Debugger},
  USymbolesTable in 'USymbolesTable.pas',
  UCompiler in 'UCompiler.pas',
  UMsg in 'UMsg.pas',
  USynParser in 'USynParser.pas',
  UNodesBase in 'UNodesBase.pas',
  UCommon in 'UCommon.pas',
  UTypes in 'UTypes.pas',
  UPreProcessor in 'UPreProcessor.pas',
  Utils in 'Utils.pas',
  UIRGen in 'UIRGen.pas',
  UExtraNodes in 'UExtraNodes.pas',
  UGenerator in 'UGenerator.pas',
  UCrc32 in 'UCrc32.pas',
  URunner in 'URunner.pas',
  UGlyphsDbg in 'UGlyphsDbg.pas' {DataModule1: TDataModule},
  USynEditEx in 'USynEditEx.pas';

{$R *.res}

begin
  Application.Initialize;
  Application.CreateForm(TDebugger, Debugger);
  Application.CreateForm(TDataModule1, DataModule1);
  Application.Run;
end.
