unit UExtraNodes;

interface
uses
   SysUtils,UNodesBase,USymbolesTable,UTypes,UIRGen,Utils;
type
   TOprExpr=class(TExpr)
   public
     Expr1,Expr2:TExpr;
   end;

   TFunctionCallExpr=class(TExpr)
   public
     ConvArgList:TExprList;
     FuncInst:TExpr;
     ObjInstance:TExpr;
     constructor Create;
     destructor Destroy; override;
   end;

   TIfStmt=class(TStmt)
   public
      Cond:TExpr;
      TrueStmt:TStmt;
      FalseStmt:TStmt;
   end;

   TWhileStmt=class(TLoopStmt)
   public
      Cond:TExpr;
      Stmt:TStmt;
   end;

   TDoStmt=class(TLoopStmt)
   public
      Cond:TExpr;
      Stmt:TStmt;
   end;
   TTryHandler=class;
   TReturnStmt=class(TStmt)
   public
      Handler:TTryHandler;
      CodeStmt:TFuncBlockStmt;
      xExprs:TExpr;
   end;

   TExprStmt=class(TStmt)
   public
     Expr:TExpr;
   end;

   TInitStmt=class(TStmt)
   public
     Src:TExpr;
     Dst:TExpr;
   end;

   TCaseStmt=class(TStmt)
   public
      Value:TExpr;
      xExpr:TExpr;
      S:TStmt;
   end;

   TSwitchStmt=class(TLoopStmt)
   public
      DefaultStmt:TCaseStmt;
      CasesList:TStmtList;
      xExpr:TExpr;
      constructor Create();override;
      destructor Destroy();override;
      function GetCase(AIdx:integer):TCaseStmt;
   end;

   TForStmt=class(TLoopStmt)
   public
      InitExpr:TStmt; // stmtexpr
      CondExpr:TExpr;
      ExprsOpt:TStmt; // stmtexpr
      S:TStmt;
   end;

   TSimpleStmt=class(TStmt)
   public
      S:TStmt;
   end;

   TBlockStmt=class(TStmt)
   public
      S:TStmt;
      Graphs:TGraphSection;
   end;

   TLabelStmt=class(TStmt)
   public
     Section:TStmt;
         lab:TExpr;
        Stmt:TStmt;
   end;

   TPrintStmt=class(TExprStmt)
   public
      ByRef:boolean;
      DataType:TDataType;
   end;

   TInitializerExpr=class(TExpr)
   public
     Elements:TExprList;
     constructor Create;
     destructor Destroy; override;
   end;

   TTryHandler=class(TLoopStmt)
   public
      ParentLoopStmt:TLoopStmt;
      ParentTryHandler:TTryHandler;
      CodeStmt:TFuncBlockStmt;
      Exec   :TSimpleStmt;
      DefaultErrHandler:TStmt;
      Handler:TSimpleStmt;
      _EndHandler:TStmt;//for end handler line number
   end;
implementation
uses UMsg;
constructor TFunctionCallExpr.Create;
begin
  ConvArgList := TExprList.Create;
end;

destructor TFunctionCallExpr.Destroy;
begin
  ConvArgList.Free;
  inherited;
end;

{ TSwitchStmt }

constructor TSwitchStmt.Create;
begin
    inherited;
    CasesList:=TStmtList.Create;
end;

destructor TSwitchStmt.Destroy;
begin
  CasesList.Free;
  inherited;
end;

function TSwitchStmt.GetCase(AIdx: integer): TCaseStmt;
begin
   Result :=TCaseStmt(CasesList.List.GetItem(AIdx));
end;

{ TInitializerExpr }

constructor TInitializerExpr.Create;
begin
   inherited;
   Elements := TExprList.Create;
end;

destructor TInitializerExpr.Destroy;
begin
  Elements.Free;
  inherited;
end;

end.
