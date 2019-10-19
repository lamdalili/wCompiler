unit UCompiler;

interface
uses SysUtils,classes,Utils, ULexParser,USynParser,UPreProcessor,USymbolesTable,UCommon, dialogs,
     UNodesBase,UTypes,UExtraNodes,UIRGen,UGenerator,URunner;

type
  TMainComp=class;
  TFuncHeaderInf=record
     Header:TSymIdent;
     Exists:boolean;
     _Name:string;
  end;
  TIRGenerator=class;
  TObjsGenerator =class;
  TErrSync=(esMain,esHeader,esSource,esStruct,esLocal);
  TComp=class(TPreProcessor)
  private
    FMainComp:TMainComp;
    FStacks:TStacks;
    FUnit:TBaseUnit;
    FStaticInitializer:TExprList;
    FSymSearch:TSymSearchList;
    FStmtsJumps:TLoopStmt;
    FActiveFunc:TFuncBlockStmt;
    FErrSyncPos:integer;
    FGenerator:TObjsGenerator;
    FGenereted :boolean;
    FActiveTryHandler:TTryHandler;
    FActiveSection :TSimpleStmt;
    function IsClassScope: boolean;
    function IsGlobalScope: boolean;
    procedure Check_Class_Symbol(AMember: TSymIdent;AImpl:TIntrfImplementation; AClass: TClassStmt);
    procedure CheckOverloadFuncCall(AFunc: TSymIdent;ActualArgs: TExprList; var Entry: TSymIdent);
    function GetFuncSignature(AEntry: TSymIdent; AFunc: TFuncType;AMustExists:boolean):TSymIdent;
    function BaseExpr: TExpr;
    procedure BuildClassTable(AClass: TClassStmt);
    function FindOverloadFunc(const AName:string;AScope:TScope;AFunc:TFuncType;AMustExists:boolean):TSymIdent;
    function NewConstructor: TOprExpr;
    function _CreateIntfFuncsTable(AClass: TClassStmt;ATable: TIntrfImplementation): TSymIdent;
    function NewStaticAddr(ASym: TSymIdent): TExpr;
    function NewInt32(AValue: integer): TExpr;
    function _CreateClassVirtualTable(AClass: TClassStmt): TSymIdent;
    function IsInterfaceScope: boolean;
    function PutInternalSymbol(AClass:TClassStmt;AList:TInitializerExpr): TSymIdent;
    function InterfaceFuncSelector:TIntrfImplementation;
    function GetSelfExpr(AType:TDataType): TExpr;
    procedure SetSymProps(ASym:TSymIdent;const AName:string;AModifiers:TDclModifiers;dt:TDataType);
    function _CreateIntrfVTable(AClass: TClassStmt): TSymIdent;
    function IsExpr(AExpr: TExpr): TExpr;
    function AsExpr(AExpr: TExpr): TExpr;
    function BaseDynTypePromotionExpr(AExpr: TExpr): TExpr;
    function MakeMetaClassType(ADest: TClassType): TDataType;
    function MetaClass: TDataType;
    function Simple_StmtList: TStmtList;
    function PrimaryBaseExpr: TExpr;
    function __NewNodeTypeConv(AExpr: TExpr; AType: TDataType): TExpr;
    function AllocatTemp(AType: TDataType): TExpr;
    function GetCurrentStmtsJumps: TLoopStmt;
    function Try_HandlerSection(): TSimpleStmt;
  protected
    function MakeRef(AExpr: TExpr;AType:TDataType): TExpr;
    function Print_Stmt: TStmt;
    function NewBaseIncrExpr(AOp:TQsCmdInst;AExpr,AFactor: TExpr): TExpr;
    function ParseChar: Char;
    function ConstStringOperation(AOp:TQsCmdInst;Expr1,Expr2:TExpr;var AOut: TExpr): boolean;
    function MakeStringType(ALen: integer): TArrayType;
    function NewInitializer(AType: TDataType; AStatic: boolean): TExpr;
    function NewInitializerListExpr():TInitializerExpr;
    function AbsoluteFuncSelector(AModifiers:TDclModifiers):TFuncHeaderInf;
    function GetActiveObject: TAllocDeclStmt;
    function MakeAbsolutIndex(ASym:TSymIdent): TExpr;
    procedure ValidateSymbol(ASym: TSymIdent);
    procedure ValidateGlobalBlock;
    function GetModifiers: TDclModifiers;
    function Class_Stmt(ATypeName:TSymIdent): TClassStmt;
    function Interface_Stmt(ATypeName:TSymIdent): TInterfaceStmt;
    function NewMemberExpr(AExpr1: TExpr;AMember:TSymIdent): TExpr;
    procedure AllocateStatic(lvar: TExpr);
    procedure AllocateLocal(lvar: TExpr);
    function NewOffsetExpr(AExpr1, AExpr2: TExpr;dt:TDataType): TExpr;
    function MemberPtrExpr(PrevExpr: TExpr): TExpr;
    procedure RearangeConst(var AOp: TQsCmdInst; var Expr1, Expr2: TExpr);
    function MakeIntBaseType(ASize: integer; ABits: TBitsClass): TExpr;
    function MakeArrayType(ADest:TDataType;ALen:integer;IdxType:TDataType):TArrayType;
    function MakeBitFieldType(ADest:TDataType;ALen:integer):TBitField;
    function MakePointerType(ADest:TDataType):TDataType;
    function MakeIntType(ASize:integer;Signed:boolean):TExpr;
    function NewConstExpr: TExpr;
    function NewExpr:TExpr;overload;
    function NewExpr(AOp: TQsCmdInst; expr1, expr2: TExpr): TOprExpr;overload;
    function NewExpr(AOp: TQsCmdInst): TExpr; overload;
    function NewLiteralExpr(AValue:integer):TExpr; overload;
    function NewLiteralExpr(const AValue:double):TExpr; overload;
    function NewLiteralExpr(AValue:char):TExpr; overload;
    function NewLiteralExpr(AValue:Pointer):TExpr;overload;
    function NewLiteralExpr(AValue:boolean):TExpr;overload;
    function NewLiteralExpr(const AValue: string): TExpr;overload;
    function RelEquConstOptimize(AOp: TQsCmdInst; Expr1, Expr2: TExpr;var AOut: TExpr): boolean;
    function BoolExprEval(AOp: TQsCmdInst; Expr1, Expr2: TExpr; var AOut: TExpr): boolean;
    function IntExprEval(AOp: TQsCmdInst; Expr1, Expr2: TExpr;var AOut: TExpr): boolean;
    function BaseConstantExprEval(AOp: TQsCmdInst; Expr1, Expr2: TExpr;var AOut: TExpr): boolean;
    function NewImplicitExpr(Src: TExpr;Dest:TDataType): TExpr;
    function FloatExprEval(AOp: TQsCmdInst; Expr1, Expr2: TExpr;var AOut: TExpr): boolean;
    function ArithLogicConstOptimize(AOp: TQsCmdInst; Expr1,Expr2: TExpr;var AOut:TExpr):boolean;
    function NewPostIncrExpr(AOp: TQsCmdInst; AExpr: TExpr): TExpr;
    function NewPreIncrExpr(AOp: TQsCmdInst; AExpr,AFactor: TExpr): TExpr;
    function NewBooleanExpr(AOp: TQsCmdInst; AExpr1, AExpr2: TExpr): TExpr;
    procedure Warning_Bool_Eval(Value:boolean);
    function NewBinBaseExpr(AOp:TQsCmdInst;AExpr1, AExpr2: TExpr): TExpr;
    function ConstImplicitConv(Src: TExpr;Dest:TDataType;var AOut: TExpr): boolean;
    function ConstExplicitConv(Src: TExpr;Dest:TDataType;var AOut: TExpr): boolean;
    function IntConstConv(IntSrc: TExpr; IntDest: TDataType): TExpr;
    function NewImplicitConv(AExpr: TExpr;AType:TDataType): TExpr;
    function NewPlusExpr(AExpr:TExpr):TExpr;
    function NewAddrExpr(AExpr:TExpr):TExpr;
    function NewDerefExpr(AExpr:TExpr):TExpr;
    function NewElementAccessExpr(AExpr1,AExpr2:TExpr):TExpr;
    function NewFieldAccessExpr(AExpr1,AExpr2:TExpr):TExpr;
    function NewCastExpr(AExpr:TExpr;Dest:TDataType):TExpr;
    function NewAssignExpr(AExpr1,AExpr2:TExpr):TExpr;
    function NewCallExpr(AFuncInf: TExpr;ArgsList: TExprList):TFunctionCallExpr;
    function NewTestExpr(AExpr1,AExpr2,AExpr3:TExpr):TExpr;
    function GetActiveFuncBlock: TFuncBlockStmt;
    function CreateTypeInfo:TDataType;
    function FunctionBlock(AFunc:TSymIdent):TBlockStmt;
    function Block():TStmt;
    function StmtList():TStmtList;
    function TypeDecl(AModifiers:TDclModifiers):TDataType;
    function IsTypeSpecifier(AExtraDcl:boolean=False):boolean;
    procedure Type_Stmt(AModifiers:TDclModifiers);
    procedure Var_Stmt(AModifiers:TDclModifiers);
    procedure Func_Stmt(AModifiers:TDclModifiers);
    function NewLocalInitializer(ADest:TExpr):TStmt;
    procedure ExitScope();
    function NewScope(AScopeClass:TAllocDeclStmtClass):Pointer;
    function NewSymbol(const AName:string;ASection:TListKind;AModifiers:TDclModifiers;dt:TDataType):TSymIdent;
    function Struct_Stmt():TStructStmt;
    function Event_Stmt(AModifiers:TDclModifiers):TDatatype;
    procedure Const_Stmt(AModifiers:TDclModifiers);
    procedure Var_Dcl(AModifiers:TDclModifiers);
    procedure ModifiersCheck(AModifiers, sTest:TDclModifiers);
    function ArgsListDcl(ADest:TDataType;AModifiers:TDclModifiers):TAllocDeclStmt;
    function ExtentedType_Dcl():TDatatype;
    function Enum_Stmt:TAllocDeclStmt;
    function GetID(const AName:string;var AOut:TExpr;TypeSelector,ARequired:boolean):boolean;
//    function LongTypeID(const AName:string;var AOut:TExpr;ARequired:boolean):boolean;
    function Expression(AMove, Required: boolean): TExpr;
    function Expr_Stmt: TStmt;
    function Stmt(AMove,ARequired:boolean): TStmt;
    function IsLabelStmt: boolean;
    function ConditionExpr: TExpr;
    function Continue_Stmt: TStmt;
    function Do_Stmt: TStmt;
    function For_Stmt: TStmt;
    function GoTo_Stmt: TStmt;
    function If_Stmt: TStmt;
    function Return_Stmt: TStmt;
    function Switch_Stmt: TStmt;
    function While_Stmt: TStmt;
    function Label_Stmt: TStmt;
    function Break_Stmt: TStmt;
    function Try_Stmt: TStmt;
    function Throw_Stmt: TStmt;
    function ExpressionList(ADest: TExprList): integer;
    function SizeOfExpr: TExpr;
    procedure EnterScope(AObj: TAllocDeclStmt; ALists: TListKindSet);
    function NewActualArgsList: TExprList;
    function ExpectConstantExpr: TExpr;
    function GetLabel:TLabelStmt;
    procedure ValidateBlock(ABlock: TAllocDeclStmt);
    function NewResBucket: TResBucket;
    function FuncProcessHeader(AModifiers: TDclModifiers): TFuncHeaderInf;
    function TxtToStaticStorage(ATxtExpr:TExpr):TExpr;
    function InternalAddr(AExpr:TExpr):TExpr;
 protected
    function GetNameStacks(AIdx: TListKind): TAllocDeclStmt;
    function GetActiveCodeStmt:TStmtList;
    function GetActiveErrSync:TErrSync;
    property ActiveFunc:TFuncBlockStmt read GetActiveFuncBlock;
    function GetSymByTag(AIdx:integer):TSymident;
 protected
    function NewStmt(QsCmdInst: TQsCmdInst; AClass: TStmtClass):Pointer;
    function AnonymousType(AType:TDataType):TExpr;
    function LiteralConstExpr:TExpr;
    function PrimaryExpr:TExpr;
    function IdentExpr():TExpr;
    function GetUnary: TExpr;
    function ParanthesizedExpr: TExpr;
    function PostFixExpr(PrevExpr:TExpr):TExpr;
    function PostDecExpr(PrevExpr:TExpr):TExpr;
    function PostIncExpr(PrevExpr:TExpr):TExpr;
    function InvocationExpr(PrevExpr:TExpr):TExpr;
    function ElementAccessExpr(PrevExpr: TExpr): TExpr;
    function MemberAccessExpr(PrevExpr: TExpr): TExpr;
    function CastExpr:TExpr;
    function UnaryExpr(AMove, Required:boolean):TExpr;
    function AdditiveExpr(AExpr:TExpr): TExpr;
    function AssignExpr(AExpr:TExpr): TExpr;
    function BoolExpr(AExpr:TExpr): TExpr;
    function RelationalExpr(AExpr:TExpr): TExpr;
    function EqualityExpr(AExpr:TExpr): TExpr;
    function LogicExpr(AExpr:TExpr): TExpr;
    function MultiplicativeExpr(AExpr:TExpr): TExpr;
    function ShiftExpr(AExpr:TExpr): TExpr;
    function TestExpr(AExpr:TExpr): TExpr;
    procedure ErrorSync();
    procedure CreateUnit;virtual;abstract;
    procedure CompileSection;virtual;abstract;
    procedure UsesStmt;virtual;abstract;
    property NameStacks[AIdx:TListKind]:TAllocDeclStmt read GetNameStacks;
    function IsPtrLink(AExpr:TExpr):boolean;
  public
    OutputStream:TMemoryStream;
    TxtVersion:integer;
    constructor Create(AMainComp:TMainComp;const AName:string);
    destructor Destroy();override;
    procedure StartDecls(AList:TStrings=nil); virtual;
    function UnitChanged():boolean;
  end;

  TUnitState= (ssHeaderSec,ssSourceSec,ssCompiled);
  TUnitComp=class(TComp)
  protected
    FImplPos:integer;
    FLoadingUses:boolean;
    ProcesssedCode:string;
    function ExportUnitBin:integer;
    procedure ProcessHeaderSection;
    procedure ProcessSourceSection;
    procedure UsesStmt;override;
    procedure CreateUnit;override;
    procedure CompileSection;override;
  public
    State:TUnitState;
  end;

  TMainComp=class(TComp)
  private
    ObjectClass:TClassStmt;
    procedure AllocateUnit(BinObj: TBinObj);
    procedure Alloc_(AComp: TComp; AStream: TStream);
    procedure CheckLoadedUnit(UnitInfo: TUnitInfo);
    function LoadedUnits(ATag: integer): TUnitComp;
    function FindPatchedSym(AExpr: TExpr): TObjSymInfo;
  protected
    procedure UsesStmt;override;
    procedure CompileSection;override;
    function GetExprUnit(AExpr:TExpr):TComp;
  public
    MainFunc:TSymIdent;
    _CompList:TQSList;
    CompsNames:TScope;
    LoadUnitCode:function (const AName: string;AComp:TComp): string of object;
    SaveUnitCode:procedure(const AName,CompiledTxt:string) of object;
    constructor Create(const AName:string);
    destructor Destroy();override;
    procedure CreateUnit;override;
    procedure LoadUnit(const AName:string;ADest:TBaseUnit);
    function Build():boolean;
    function Comps(idx: integer): TComp;
  end;

  TIRGenerator=class
  private
    FLabels:TList;
    FComp:TComp;
    FGraphsList:TGraphSection;
    FActiveStmt:TStmt;
    FActiveFunc:TFuncBlockStmt;
    FActiveGraph:TGraphRec;
    _TmpLabs:TList;
    Line:integer;
    function GetLabAsGraph(ALab:integer):TGraphRec;
    function NewLabel():integer;
    procedure JumpsExprVisit(AExpr: TExpr;AFalseLab: integer);
    procedure EmitLabel(ALab: integer);
    procedure Jump(ALab: integer);
    procedure FuncVisit(AFuncBlock: TFuncBlockStmt);
    procedure StmtVisit(AStmt: Pointer);
    procedure Gen(Op: TQsCmdInst; A1, A2: TExpr);
    function ExprVisit(AExpr: TExpr;LValue:boolean):TExpr;
    procedure If_Visit(AStmt: TIfStmt);
    procedure While_Visit(AStmt:TWhileStmt);
    procedure Do_Visit(AStmt: TDoStmt);
    procedure ExprStmt_Visit(AStmt: TExprStmt);
    procedure StmtList_Visit(AStmt: TStmtList);
    procedure GoTo_Visit(AStmt: TSimpleStmt);
    procedure Break_Visit(AStmt: TStmt);
    procedure Continue_Visit(AStmt: TStmt);
    procedure Return_Visit(AStmt: TReturnStmt);
    procedure For_Visit(AStmt: TForStmt);
    procedure LabelStmt_Visit(AStmt: TLabelStmt);
    procedure ExprInitStmt_Visit(AStmt: TInitStmt);
    function Call_Visit(ACall: TFunctionCallExpr):TExpr;
    procedure SwitchStmt_Visit(AStmt: TSwitchStmt);
    procedure BuidGraph;
    procedure GetUsedExprs(Vars:TBitsSet; AIR: TCompNode;ADest:TExpr);
    procedure Report_NotUsed_Value(AExpr:TExpr;AIR:TCompNode);
    procedure LivenessAnalyse;
    procedure Report_uninitialized(AExpr: TExpr; AIR: TCompNode);
    procedure intis_Exprs(usedvars: TBitsSet; AIR: TCompNode;ADest:TExpr);
    procedure InitializationAnalyse;
    function JumpsToBool(AExpr: TExpr):TExpr;
    procedure FuncBlockVisit(AStmt: TBlockStmt);
    function NewTemp(dt:TDataType): TExpr;
    function OpExprVisit(AExpr: TExpr):TExpr;
    function NewGraph:integer;
    procedure StmtCreateLabels(AStmt: Pointer);
    procedure StmtGen(AStmt: Pointer);
    procedure AddIR(O: TCompNode);
    procedure _JumpsExprVisit(AExpr: TExpr; ATrueLab, AFalseLab: integer);
    procedure GenCopy(Dest, Src: TExpr);
    procedure Print_Visit(AStmt: TPrintStmt);
    procedure TryFinally_Visit(AStmt: TTryHandler);
    function LoopExitHandler(AStmt: TLoopStmt): TLoopStmt;
    procedure ExitTry(AStmt: TTryHandler);
    procedure TryExcept_Visit(AStmt: TTryHandler);
    procedure Throw_Visit(AStmt: TExprStmt);
    procedure _LivenessAnalyse;
  public
    constructor Create(AComp: TComp);virtual;
    destructor Destroy();override;
    procedure CodeGen(AList:TStrings);
  end;

  TObjsGenerator=class(TIRGenerator)
  private
    procedure LoadOprnd(AExpr: TExpr; AReg: TRegDest);
    procedure SaveOprnd(AExpr: TExpr; AReg: TRegDest);
    procedure OperationGen(AOp:TQsCmdInst;dt: TDataType);
    procedure Incrementation(AExpr,AFactor:TExpr;ADirection:boolean);
    procedure MakeExprAddr(ARest :TByteRec;AExpr: TExpr);
    function SymIndex(AExpr: TExpr): TMcLoc;
    procedure ProcessGraph(AGrphs:TGraphSection;Labels:TQSList);
    procedure Condition(AExpr:TOprExpr);
    procedure Loadlabel(lab: integer; AReg: TRegDest);
    procedure LoadAddr(AExpr: TExpr; AReg: TRegDest);
    procedure LoadParam(AExpr: TExpr);
    procedure PushResultAddr(AExpr: TExpr);
    procedure McCopy(AExpr: TOprExpr);
    procedure LineNumberGen(AExpr: TOprExpr);
  public
    BinObj:TBinObj;
    constructor Create(AComp: TComp);override;
    destructor Destroy();override;
    procedure MakeObj();
  end;

implementation
uses UMsg,UCrc32,USynEditEx;

function CompatibleType(t1,t2:TDataType;out Conv:TDataType;AOperator:TQsCmdInst=imNone):boolean;
var
 t:TDataType;
begin
    Conv :=nil;
    if t1.TypeClass <> t2.TypeClass then
    begin
       if t1.IsNumericType()and t2.IsNumericType()then
          Conv := FloatType.DataType
       else if not t1.IsMethodType and not t2.IsMethodType then
       begin
           if t1.IsUnTypedPointer then
           begin
               if t2.TypeClass in [tcArray,tcFuncType,tcClass,tcInterface,tcClassRef] then
                  Conv := PtrType.DataType
           end else if t2.IsUnTypedPointer then
           begin
               if t1.TypeClass in [tcArray,tcFuncType,tcClass,tcInterface,tcClassRef] then
                  Conv := PtrType.DataType
           end;
       end;
    end else
      case t1.TypeClass of
            tcChar:Conv := CharType.DataType;
           tcFloat:Conv := FloatType.DataType;
            tcBool:Conv := BoolType.DataType;
          tcEnum:begin
                if t1 = t2 then
                   Conv :=t1;
           end;
           tcInteger:begin
               if AOperator in [imShr,imShl] then
               begin
                 Conv:= t1;
               end else begin
                if (itSigned in t1.BitsClass)<>(itSigned in t2.BitsClass) then
                begin
                   t1 :=SelectSignedIntType(t1).DataType;
                   t2 :=SelectSignedIntType(t2).DataType;
                end;
                Conv:= SelectSubIntType(t1).DataType;
                  t := SelectSubIntType(t2).DataType;
                if Conv.TypeSize< t.TypeSize then
                   Conv:=t;
              end;
           end;
          tcFuncType:begin
                if TFuncType(t1).IsEqual(t2) then
                   Conv :=t1;
           end;
          tcPointer:begin
                if t1.IsUnTypedPointer or t2.IsUnTypedPointer then
                   Conv := PtrType.DataType
                else if t1.Dest = t2.Dest then
                   Conv :=t1;
           end;
          tcArray:begin
                if t1.Dest = t2.Dest then
                   Conv :=t1;
           end;
          tcClassRef:begin
                if t1.Dest = t2.Dest then
                   Conv :=t1;
           end;
          tcInterface:begin
                   Conv :=PtrType.DataType;
           end;
           tcClass:begin
                  if TClassType(t1).IsInstanceOf(t2)then
                     Conv :=t2
                  else if TClassType(t2).IsInstanceOf(t1)then
                     Conv :=t1;
           end;
      end;
    Result :=  Conv <> nil;
end;

function CompatibleAssign(ASourceType,ADestType:TDataType;AExplicit:boolean):boolean;
begin
   Result := False;
   with ASourceType do
     if ASourceType= ADestType then
         Result := True
     else if IsIntType then
         Result := ADestType.IsNumericType()
     else if IsBool then
         Result := ADestType.IsBool()
     else if ADestType.IsFuncType()then
         Result := (IsFuncType()and TFuncType(ADestType).IsEqual(ASourceType))
                   or (IsUnTypedPointer() and not ADestType.IsMethodType)
     else if ADestType.IsUnTypedPointer()then
         Result := IsPointer()or IsClsIntrfType()or IsMetaClass()
     else if IsPointer()and ADestType.IsPointer() then
         Result := IsUnTypedPointer()or ADestType.IsUnTypedPointer()
                   or(Dest = ADestType.Dest)
     else if IsArray()and ADestType.IsOpenArray() then
         Result := Dest=ADestType.Dest
     else if IsClass and ADestType.IsClass  then
         Result := TClassType(ASourceType).IsInstanceOf(ADestType)
     else if IsClass and ADestType.IsInterface() then
         Result := TClassType(ASourceType).Support(ADestType)
     else if IsUnTypedPointer()and ADestType.IsMetaClass() then
         Result := True
     else if ADestType.IsClass and IsUnTypedPointer()then
         Result :=True
     else if IsMetaClass and  ADestType.IsMetaClass()then
         Result := TClassType(ASourceType.Dest).IsInstanceOf(ADestType.Dest)
     else if IsArray()and ADestType.IsArray() then
         Result := (Dest=ADestType.Dest)
                 ;//   and(TArrayType(ASourceType).Count = TArrayType(ADestType).Count);

    if not Result and AExplicit then
     with ASourceType do
     begin
         if IsIntType then
             Result := ADestType.TypeClass in[tcBool,tcEnum,tcChar,tcPointer]
         else if ADestType.IsIntType()then
             Result := TypeClass in[tcBool,tcFloat,tcEnum,tcChar,tcPointer]
         else if IsArray() and ADestType.IsArray() then
             Result :=True
         else if IsPointer() and ADestType.IsPointer() then
             Result :=True
         else if IsClass() and  ADestType.IsClsIntrfType() then
             Result :=True
     end;
end;

function BaseOperationType(AOperator:TQsCmdInst;dt:TDataType):TDataType;
begin
  Result :=nil;
  with dt do
    case AOperator of
       imAdd,imMul,imDiv:
          if TypeClass = tcFloat then
             Result :=FloatType.DataType
          else if TypeClass = tcInteger then
                  if itSigned in BitsClass then
                     Result :=IntType.DataType
                  else
                     Result :=UIntType.DataType;
       imPlus:
          if TypeClass in [tcInteger,tcFloat]then
             Result :=dt;
       imMinus,imSub,imModul:
          if TypeClass = tcFloat then
             Result :=FloatType.DataType
          else if TypeClass = tcInteger then
             Result :=IntType.DataType;
       imShl,imShr:
          if TypeClass = tcInteger then
             if itSigned in BitsClass then
                    Result :=IntType.DataType
                  else
                    Result :=UIntType.DataType;
       imAnd,imOr,imComp:
          if TypeClass = tcInteger then
             Result :=dt;
       imXor:
          if TypeClass in [tcInteger,tcBool]then
             Result :=dt;
       imPreInc,imPreDec,imPostInc,imPostDec:
          if IsOrdinalType() or dt.IsTypedPointer() then
             Result :=dt;
       imLess,imGr,imLessEqu,imGrEqu:
          if IsRangeType()then
             Result :=BoolType.DataType;
       imEqu,imNotequ:
          if TypeClass in [tcInteger,tcPointer,tcChar,tcBool,tcEnum,tcFloat,
                           tcClass,tcInterface,tcClassRef]then
             Result :=BoolType.DataType;
       imOrCmp,imAndCmp,imNot:
          if IsBool() then
             Result :=BoolType.DataType;
        imIs:
            if IsClsIntrfType then
               Result := BoolType.DataType;
    end;
end;
type
  TFuncCompareKind=(fcNone,fcExact,fcCompatible);
  TFuncCallStatus=(scError,scAmbiguous,scValid);
function IsValidArg(AParam,Arg:TExpr):TFuncCompareKind;
begin
  Result := fcNone;
  with AParam do
  begin
     if (QureyKind=atReference)then
     begin                          {strict type byRef}
       if not Arg.IsAddressable()or not IsTypeEqual(DataType,Arg.DataType) then
          Exit;
     end;
     if IsTypeEqual(DataType,Arg.DataType)then
        Result := fcExact
     else if CompatibleAssign(Arg.DataType,DataType,False)then
        Result := fcCompatible
  end;
end;

function IsValidFuncCall(AFunc:TExpr;ActualArgs:TExprList):TFuncCompareKind;
var
  Params:TTypeMembers;
  I:integer;
  Param:TExpr;
begin
   Result := fcNone;
   if not AFunc.DataType.IsFuncType then//  [added ]
      Exit;
   Params :=AFunc.DataType as TTypeMembers;
   if Params.Members.Count < ActualArgs.Count then
      Exit;
   if Params.Members.Count > ActualArgs.Count then // add args with default values
     for I := ActualArgs.Count to Params.Members.Count-1 do
     begin
       Param :=Params.Members.GetExpr(I);
       if Param.Value.vPtr = nil then // must have default value
          Exit;
       ActualArgs.AddExpr(TExpr(Param.Value.vPtr));
     end;
   Result := fcExact;
   for I := 0 to ActualArgs.Count-1 do
   begin
      Param := Params.Members.GetExpr(I);
      case IsValidArg(Param,ActualArgs.GetExpr(I))of
             fcExact: continue;
        fcCompatible: if Param.Value.vPtr <> nil then
                         continue;
      end;
      Result := fcNone;
      break;
   end;
   if Result = fcExact then
      Exit;
   for I := 0 to ActualArgs.Count-1 do
   begin
      Param := Params.Members.GetExpr(I);
      if IsValidArg(Param,ActualArgs.GetExpr(I))=fcNone then
         Exit;
   end;
   Result := fcCompatible;
end;

function _CheckOverloadFuncCall(AFunc:TSymIdent;ActualArgs:TExprList;var Entry:TSymIdent):TFuncCallStatus;
var
  Len:integer;
  C:TFuncCompareKind;
  Exact_Count:integer;
  Compatible_Count:integer;
  CompEntry:TSymIdent;
begin
   Result := scError;
   Len := ActualArgs.Count;
   Entry     :=nil;
   CompEntry :=nil;
   Exact_Count:=0;
   Compatible_Count:=0;
   while AFunc<> nil do
   begin
      ActualArgs.Count := Len;
      C := IsValidFuncCall(AFunc,ActualArgs);
      case C of
            fcExact:begin
               Inc(Exact_Count);
               Entry:=AFunc;
            end;
          fcCompatible:begin
               Inc(Compatible_Count);
               CompEntry:=AFunc;
            end;
      end;
      AFunc := AFunc.NextSym;
   end;
   if  Entry = nil then
       Entry :=CompEntry;
   if (Exact_Count>1)or((Exact_Count=0)and(Compatible_Count>1))then
       Result := scAmbiguous
   else if Entry <> nil then
           Result := scValid;
end;

procedure TComp.CheckOverloadFuncCall(AFunc:TSymIdent;ActualArgs:TExprList;var Entry:TSymIdent);
var
  Ret:TFuncCallStatus;
  AClass:TInheritedType;
begin
   Ret := _CheckOverloadFuncCall(AFunc,ActualArgs,Entry);
   if Ret = scValid then
      Exit;
   repeat
       if not(AFunc.Parent is TInheritedType)then
          break;
       FSymSearch.Text := AFunc.Name;
       AClass :=AFunc.Parent as TInheritedType;
       if not AClass.FindInheritedMember(FSymSearch) then
          break;
       AFunc := FSymSearch.Mutch;// week must check if Sym is func not var or type...
       Ret := _CheckOverloadFuncCall(AFunc,ActualArgs,Entry);
   until Ret = scValid;

   if Ret = scAmbiguous then
      raise ECompException.CreateRes(@AMBIG_FUNC_CALL);
   if Ret = scError then
      raise ECompException.CreateRes(@FUNC_CALL_ERROR);
end;
{ TComp }

procedure TComp.ErrorSync;
const MAIN_SYNC  =[uuFunc,uuConst,uuStatic, uuReadonly,uuEvent,uuRef,
                   uuNone,uuInstSep,uuLine,uuType];
const HEADER_SYNC=[uuFunc,uuConst,uuStatic, uuReadonly,uuEvent,uuRef,
                   uuNone,uuInstSep,uuLine,uuType];
const SOURCE_SYNC=[uuFunc,uuConst,uuStatic, uuReadonly,uuEvent,uuRef,
                   uuNone,uuInstSep,uuLine,uuType];
const STRUCT_SYNC=[uuFunc,uuConst,uuVar,uuStatic, uuReadonly,uuRef,
                   uuNone,uuInstSep,uuLine,uuType,uuClass,
                   uuInterface];
const LOCAL_SYNC =[uuNone,uuInstsep, uuLine,uuReadonly,uuEvent,
                   uuType, uuVar, uuFunc,uuConst, uuStatic,uuRef,
                   uuReturn,uuDefault, uuCase, uuSwitch,uuContinue,
                   uuBreak, uuFor,uuElse,uuDo, uuWhile, uuIf,uuEnum,
                   uuUnion,uuStruct,uuGoto,uuTry,uuClass,uuInterface];

begin
   if CurrentToken=uuNone then
      Exit;
   if FPos = FErrSyncPos then
      NextToken();
   case GetActiveErrSync() of
        esMain:while not(CurrentToken in MAIN_SYNC)do NextToken();
      esHeader:while not(CurrentToken in HEADER_SYNC)do NextToken();
      esSource:while not(CurrentToken in SOURCE_SYNC)do NextToken();
      esStruct:while not(CurrentToken in STRUCT_SYNC)do NextToken();
       esLocal:while not(CurrentToken in LOCAL_SYNC)do NextToken();
   end;
   FErrSyncPos := FPos;
end;

constructor TComp.Create(AMainComp:TMainComp;const AName:string);
begin
   inherited Create;
   FName :=AName;
   FMainComp :=AMainComp;
   CreateUnit();
   FStaticInitializer:=TExprList.Create;
   FStacks    :=TStacks.Create;
   FSymSearch:=TSymSearchList.Create;
   FGenerator:=TObjsGenerator.Create(Self);
   OutputStream:=TMemoryStream.Create;
end;

destructor TComp.Destroy;
begin
  OutputStream.Free;
  FGenerator.Free;
  FSymSearch.Free;
  FStacks.Free;
  FUnit.Free;
  FStaticInitializer.Free;
  inherited;
end;

{function TComp.GetID(const AName:string;var AOut:TExpr;ARequired:boolean):boolean;
begin
   AOut :=nil;
   FSymSearch.Text :=AName;
   Result := NameStacks[ssNamesList].Find(FSymSearch);
   if not Result  then
     if SameText(FSymSearch.Text,FUnit.Name) then
      begin
        FSymSearch.Add(FUnit);
        Result := True;
      end;
   if not Result then
   begin
     if ARequired then
        raise ECompException.CreateFmt('invalid name "%s"',[AName]);
     Exit;
   end;
   if not FSymSearch.Mutch.IsCode and (FSymSearch.Mutch.NextSym <> nil) then
      raise ECompException.CreateFmt('ambigu "%s"',[AName]);
   AOut := FSymSearch.Mutch;
end;

function TComp.LongTypeID(const AName: string; var AOut: TExpr;ARequired: boolean): boolean;
begin
   Result := GetID(AName,AOut,ARequired);
   if not Result then
      Exit;
   while not AOut.IsField() and not AOut.IsRValue and TryNextToken(uuOpDot) do   //no nested scopes (while)
   begin
        NextToken();
        if not ((AOut.DataType.SymbInfo) is TScope )then
           Err(@SCOPE_EXPECTED);
        FSymSearch.Text :=GetTokenTxt;
        if not  TScope(AOut.DataType.SymbInfo).FindMember(FSymSearch,NameStacks[ssNamesList]) then
           raise ECompException.Createfmt('can not find "%s"',[FSymSearch.Text]);
        AOut := FSymSearch.Mutch;
   end;
   AOut.Used :=True;
end;  }
function TComp.GetID(const AName:string;var AOut:TExpr;TypeSelector,ARequired:boolean):boolean;
var
 Ret:TSymIdent;
begin
   AOut :=nil;
   FSymSearch.Text :=AName;
   Result := NameStacks[ssNamesList].Find(FSymSearch);
   if not Result  then
     if SameText(FSymSearch.Text,FUnit.Name) then
      begin
        FSymSearch.Add(FUnit);
        Result := True;
      end;
   if not Result then
   begin
     if ARequired then
        raise ECompException.CreateFmt('invalid name "%s"',[AName]);
     Exit;
   end;
   if not FSymSearch.Mutch.IsCode and (FSymSearch.Mutch.NextSym <> nil) then
      raise ECompException.CreateFmt('ambigu "%s"',[AName]);
   Ret := FSymSearch.Mutch;
   while not Ret.IsField() and not Ret.IsRValue
      and ( TypeSelector or not(Ret.DataType.TypeClass in [tcClass,tcStruct]))
      and TryNextToken(uuOpDot) do
   begin
        NextToken();
        if not ((Ret.DataType.SymbInfo) is TScope )then
           Err(@SCOPE_EXPECTED);
        FSymSearch.Text :=GetTokenTxt;
        if not  TScope(Ret.DataType.SymbInfo).FindMember(FSymSearch,NameStacks[ssNamesList]) then
           raise ECompException.Createfmt('can not find "%s"',[FSymSearch.Text]);
        Ret := FSymSearch.Mutch; //only one iten
   end;
   Ret.Used :=True;
   AOut := Ret;
end;

function TComp.MakeArrayType(ADest:TDataType;ALen:integer;IdxType:TDataType):TArrayType;
begin
    Result :=TArrayType.Create;
    Result.SeBaseTypeProps(tcArray,[],0,ADest);
    Result.Count := ALen;
    Result.IndexType :=IdxType;
    AnonymousType(Result);
end;

function TComp.MakeMetaClassType(ADest:TClassType):TDataType;
begin
    Result :=TDataType.Create;
    Result.SeBaseTypeProps(tcClassRef,[],4,ADest);
    AnonymousType(Result);
end;

function TComp.MakeStringType(ALen:integer):TArrayType;
begin
    Result :=TArrayType.Create;
    Result.SeBaseTypeProps(tcArray,[],0,CharType.DataType);
    Result.Count := ALen;
    Result.IndexType :=IntType.DataType;
    Result.TypeSize :=ALen * CharType.DataType.TypeSize;
    AnonymousType(Result);
end;

function TComp.MakeBitFieldType(ADest:TDataType;ALen:integer):TBitField;
var
 bs:TBitsClass;
begin
    if not (ADest.TypeClass in [tcInteger,tcBool]) then
       Err(@BITS_FIELDS_ERROR);
    if ADest.IsBool and(ALen <> 1) then
       Err(@BITS_FIELDS_ERROR)
    else if ALen >(ADest.TypeSize * ALLOC_UNIT)  then
            Err(@BITS_FIELDS_ERROR);
    bs :=ADest.BitsClass -[itSigned];
    bs := bs+[itBitField];
    Result :=TBitField.Create;
    Result.SeBaseTypeProps(ADest.TypeClass,bs,ADest.TypeSize,nil);
    Result.BitsCount := ALen;
    AnonymousType(Result);
end;

function TComp.MakePointerType(ADest: TDataType): TDataType;
begin
    Result :=TDataType.Create;
    Result.SeBaseTypeProps(tcPointer,[it32Bit],SIZEOFPOINTER,ADest);
    AnonymousType(Result);
end;

function TComp.MakeIntBaseType(ASize:integer;ABits:TBitsClass):TExpr;
var
  D:TDataType;
begin
    D:=TDataType.Create;
    Result:=AnonymousType(D);
    D.SeBaseTypeProps(tcInteger,ABits,ASize,nil);
end;

function TComp.MakeIntType(ASize:integer;Signed:boolean):TExpr;
var
 Bits:TBitsClass;
begin
   Bits:=[];
   if Signed then
      Bits:=[itSigned];
   case ASize of
     1: Result := MakeIntBaseType(1,Bits+[it8bit]);
     2: Result := MakeIntBaseType(2,Bits+[it8bit,it16bit]);
     4: Result := MakeIntBaseType(4,Bits+[it8bit,it16bit,it32bit]);
   else
     raise ECompException.CreateRes(@INVALIDTYPE);
   end;
end;

procedure TComp.AllocateStatic(lvar: TExpr);
begin
   FUnit.Allocate(lvar);
   FStaticInitializer.Add(lvar);
   lvar.ObjLocation := olStatic;
end;

procedure TComp.AllocateLocal(lvar: TExpr);
begin
  ActiveFunc.Allocate(lvar);
  lvar.ObjLocation := olAuto;
end;

function TComp.AllocatTemp(AType: TDataType):TExpr;
begin
   if AType.IsStructArrayType then
      Msg_Report(msError,'struct or array forbiden',GetLine());
   Result := FActiveFunc.NewSymbol(TSymIdent);
   Result.SetDataType(AType);
   FActiveFunc.Allocate(Result);
   Result.ObjLocation := olTemp;
end;

function TComp.AnonymousType(AType: TDataType):TExpr;
begin
   Result :=FUnit.NewSymbol(TSymTyped);
   Result.SetDataType(AType);
   Result.ObjLocation:= olType;
end;

function TComp.NewExpr():TExpr;
begin
   Result := TExpr.Create;
   FfreeList.Add(Result);
   Result.Line :=GetLine();
end;

function TComp.NewConstExpr():TExpr;
begin
   Result := NewExpr();
   Result.ObjLocation :=olLiteral;
   Result.AccessType  :=qoReadOnly;
   Result.xOp :=imValue;
end;

function TComp.NewLiteralExpr(AValue: Pointer): TExpr;
begin
    Result := NewConstExpr();
    Result.Value.vPtr :=AValue;
    Result.SetDataType(PtrType.DataType);
end;

function TComp.NewLiteralExpr(AValue: integer): TExpr;
begin
    Result := NewConstExpr();
    Result.Value.vInt :=AValue;
    Result.SetDataType(SelectIntType(AValue).DataType);
end;

function TComp.NewLiteralExpr(AValue: char): TExpr;
begin
    Result := NewConstExpr();
    Result.Value.vChar :=AValue;
    Result.SetDataType(CharType.DataType);
end;

function TComp.NewLiteralExpr(AValue: boolean): TExpr;
begin
    Result := NewConstExpr();
    Result.Value.vBool :=AValue;
    Result.SetDataType(BoolType.DataType);
end;

function TComp.NewLiteralExpr(const AValue: double): TExpr;
begin
    Result := NewConstExpr();
    Result.Value.vFloat :=AValue;
    Result.SetDataType(FloatType.DataType);
end;

function TComp.NewLiteralExpr(const AValue: string): TExpr;
var
  Txt:string;
  St:TResBucket;
begin
     Result :=NewConstExpr();
     Txt := AValue+#0;
     St:= NewResBucket().Append(Pointer(Txt)^,Length(Txt));
     Result.Value.vPtr :=St;
     Result.SetDataType(MakeStringType(Length(Txt)));
     Result.xOp :=imTextStream;
end;

function TComp.NewExpr(AOp:TQsCmdInst):TExpr;
begin
   Result := NewExpr();
   Result.xOp :=AOp;
end;

function TComp.NewExpr(AOp:TQsCmdInst; expr1, expr2:TExpr):TOprExpr;
begin
   Result := TOprExpr.Create;
   Result.xOp :=AOp;
   TOprExpr(Result).Expr1 :=expr1;
   TOprExpr(Result).Expr2 :=expr2;
   FfreeList.Add(Result);
   Result.Line :=GetLine();
end;

function TComp.NewImplicitExpr(Src: TExpr;Dest:TDataType): TExpr;
var
 FuncEntry,Sym:TSymIdent;
 Expr,Ret:TExpr;
 IntrfField:TIntrfImplementation;
begin
   if Src.DataType = Dest then
       Result := Src
   else begin
       if not ConstImplicitConv(Src, Dest,Result) then
       begin
          if Src.IsMethod() then
          begin
              FuncEntry := TSymIdent(TOprExpr(Src).Expr2);
              Sym := GetFuncSignature(FuncEntry,Dest as TFuncType,True);
              Expr :=MakeAbsolutIndex(Sym);
              Ret := NewExpr(imNone,TOprExpr(Src).Expr1,Expr);
              Ret.Assign(Expr);
              Ret.SetDataType(Expr.DataType);
              Src := Ret;
          end else if Src.IsCode then
          begin  // select correct overload entry
              FuncEntry := TSymIdent(Src);
              Sym := GetFuncSignature(FuncEntry,Dest as TFuncType,True);
              Expr :=MakeAbsolutIndex(Sym);
              Src := Expr;
          end else if Src.DataType.IsClass and Dest.IsInterface then
          begin
              TClassStmt(Src.DataType.SymbInfo).Support(Dest,IntrfField);
              Src:= NewAddrExpr(NewMemberExpr(Src,IntrfField));
          end;
          Result := NewExpr(imImplicit,Src,nil);
          Result.SetDataType(Dest);
          Result.ObjLocation := olTemp;
      end;
   end;
end;

function TComp.RelEquConstOptimize(AOp:TQsCmdInst;Expr1, Expr2:TExpr;var AOut:TExpr):boolean;
var
 LeftType:TDataType;
begin
     Result :=False;
     AOut := nil;
     if Expr2=nil then
        Exit;
     if not Expr1.DataType.IsRangeType
        or not Expr2.DataType.IsRangeType then
           Exit;
     if not Expr2.IsConstant then
        Exit;
     LeftType :=Expr1.DataType;
     if Expr2.AsNumber < LeftType.Min_Range then
     begin
        case AOp of
            imEqu: AOut:= NewLiteralExpr(False);
         imNotequ: AOut:= NewLiteralExpr(True);
             imGr: AOut:= NewLiteralExpr(True);//
           imLess: AOut:= NewLiteralExpr(False);//
          imGrEqu: AOut:= NewLiteralExpr(True);
        imLessEqu: AOut:= NewLiteralExpr(False);
        end
     end else if Expr2.AsNumber > LeftType.Max_Range then
     begin
        case AOp of
            imEqu: AOut:= NewLiteralExpr(False);
         imNotequ: AOut:= NewLiteralExpr(True);
             imGr: AOut:= NewLiteralExpr(False);
           imLess: AOut:= NewLiteralExpr(True);
          imGrEqu: AOut:= NewLiteralExpr(False);
        imLessEqu: AOut:= NewLiteralExpr(True);
        end;
     end else if (AOp = imLess)and(Expr2.AsNumber = LeftType.Min_Range) then
         AOut:= NewLiteralExpr(False)
     else if (AOp = imGr)and(Expr2.AsNumber = LeftType.Max_Range) then
         AOut:= NewLiteralExpr(False);

     Result := AOut <> nil;
end;

procedure TComp.RearangeConst(var AOp:TQsCmdInst;var Expr1, Expr2:TExpr);
var
  tmp :TExpr;
begin
    if Expr1.IsConstant and(AOp in [ imAdd,imMul,imAnd,imOr,imXor,
                                     imEqu,imNotEqu,
                                     imLess,imGr,imLessEqu,imGrEqu]) then
    begin
         tmp := Expr1;
       Expr1 := Expr2;
       Expr2 := tmp;
       case AOp of
            imLess: AOp:=imGrEqu;
           imGrEqu: AOp:=imLess;
              imGr: AOp:=imLessEqu;
         imLessEqu: AOp:=imGr;
       end;
    end;
end;

function TComp.ArithLogicConstOptimize(AOp:TQsCmdInst;Expr1, Expr2:TExpr;var AOut:TExpr):boolean;
var
  v:int64;
  shift:integer;
begin
    AOut := nil;
    if (Expr2<>nil) and  Expr2.IsConstant then
    begin
        if Expr2.DataType.IsNumericType then
        begin
            if (AOp in [imModul,imDiv]) and (Expr2.AsNumber=0) then
                Msg_Report(msError,@DIV_BY_ZERO);
            if((AOp in [imMul,imDiv])and(Expr2.AsNumber = 1))   //Arth optimization
              or((AOp in [imAdd,imSub,imOr,imXor,imShl,imShr])and(Expr2.AsNumber = 0))
              or(Expr2.DataType.IsIntType and(AOp = imAnd)and(Expr2.Value.vInt = -1))then
                 AOut := Expr1
            else if (AOp = imMul)and(Expr2.AsNumber = 0) then
            begin
                AOut := NewLiteralExpr(0.0);
                AOut.SetDataType(Expr1.DataType);
            end else if Expr2.DataType.IsIntType and (AOp in [imMul,imDiv]) then
            begin  // power 2 mul & div
                v:= Expr2.Value.vInt64;
                if (v and (v-1)) = 0 then
                begin
                    shift:=-1;
                    repeat
                       v := v shr 1;
                       inc(shift);
                    until v=0;
                    case AOp of
                       imMul:AOut := NewExpr(imShl,Expr1,NewLiteralExpr(shift));
                       imDiv:AOut := NewExpr(imShr,Expr1,NewLiteralExpr(shift));
                    end;
                    AOut.SetDataType(Expr1.DataType);
                    AOut.ObjLocation := olTemp;
                end;
            end;
        end else if Expr2.DataType.IsBool then
        begin
            if (AOp = imXor )and(not Expr2.Value.vBool)then
               AOut :=Expr1
        end;
    end else if Expr1.IsConstant then
    begin
        if Expr1.DataType.IsBool then
        begin
            if ((AOp in [imOrCmp,imXor] )and(not Expr1.Value.vBool)) // false (or|xor) Expr
                or ((AOp = imAndCmp)and(Expr1.Value.vBool))then      // true and Expr
                   AOut :=Expr2
            else if (AOp = imOrCmp)and Expr1.Value.vBool then       // true or Expr
                AOut := NewLiteralExpr(True)
            else if (AOp = imAndCmp )and (not Expr2.Value.vBool) then // false and Expr
                AOut := NewLiteralExpr(False)
        end;
    end;
    Result := AOut <> nil;
end;

function TComp.BoolExprEval(AOp:TQsCmdInst;Expr1, Expr2:TExpr;var AOut:TExpr):boolean;
begin
  AOut := nil;
  if Expr1.IsConstant then
  begin
    if AOp=imNot then
       AOut := NewLiteralExpr(not Expr1.Value.vBool)
    else if (Expr2<>nil)and Expr2.IsConstant then
        case AOp of
            imXor:AOut := NewLiteralExpr(Expr1.Value.vBool xor Expr2.Value.vBool);
            imEqu:AOut := NewLiteralExpr(Expr1.Value.vBool=Expr2.Value.vBool);
         imNotequ:AOut := NewLiteralExpr(Expr1.Value.vBool<>Expr2.Value.vBool);
          imOrCmp:AOut := NewLiteralExpr(Expr1.Value.vBool or  Expr2.Value.vBool);
         imAndCmp:AOut := NewLiteralExpr(Expr1.Value.vBool and Expr2.Value.vBool);
        end;
  end;
  Result := AOut <> nil;
end;

function TComp.IntExprEval(AOp:TQsCmdInst;Expr1, Expr2:TExpr;var AOut:TExpr):boolean;
begin
  AOut := nil;
  if Expr1.IsConstant then
   case AOp of
      imMinus:AOut := NewLiteralExpr(-Expr1.AsInteger);
      imPlus :AOut := Expr1;
      imComp :AOut := NewLiteralExpr(not Expr1.AsInteger);
      else if (Expr2<>nil)and Expr2.IsConstant then
          case AOp of
              imAdd:AOut := NewLiteralExpr(Expr1.AsInteger + Expr2.AsInteger);
              imSub:AOut := NewLiteralExpr(Expr1.AsInteger - Expr2.AsInteger);
              imMul:AOut := NewLiteralExpr(Expr1.AsInteger * Expr2.AsInteger);
            imModul:AOut := NewLiteralExpr(Expr1.AsInteger mod Expr2.AsInteger); // div by zero
              imDiv:AOut := NewLiteralExpr(Expr1.AsInteger div Expr2.AsInteger); // div by zero
              imAnd:AOut := NewLiteralExpr(Expr1.AsInteger and Expr2.AsInteger);
               imOr:AOut := NewLiteralExpr(Expr1.AsInteger or  Expr2.AsInteger);
              imXor:AOut := NewLiteralExpr(Expr1.AsInteger xor Expr2.AsInteger);
              imShl:AOut := NewLiteralExpr(Expr1.AsInteger shl Expr2.AsInteger);
              imShr:AOut := NewLiteralExpr(Expr1.AsInteger shr Expr2.AsInteger);
              imEqu:AOut := NewLiteralExpr(Expr1.AsInteger = Expr2.AsInteger);
             imLess:AOut := NewLiteralExpr(Expr1.AsInteger < Expr2.AsInteger);
               imGr:AOut := NewLiteralExpr(Expr1.AsInteger > Expr2.AsInteger);
           imNotequ:AOut := NewLiteralExpr(Expr1.AsInteger <> Expr2.AsInteger);
          imLessEqu:AOut := NewLiteralExpr(Expr1.AsInteger <= Expr2.AsInteger);
            imGrEqu:AOut := NewLiteralExpr(Expr1.AsInteger >= Expr2.AsInteger);
          end
   end;
  Result := AOut <> nil;
end;

function TComp.FloatExprEval(AOp:TQsCmdInst;Expr1, Expr2:TExpr;var AOut:TExpr):boolean;
begin
  AOut := nil;
  if Expr1.IsConstant then
   case AOp of
      imMinus:AOut := NewLiteralExpr(-Expr1.Value.vFloat);
      imPlus :AOut := Expr1;
      else if (Expr2<>nil)and Expr2.IsConstant() then
         case AOp of
            imAdd:AOut := NewLiteralExpr(Expr1.Value.vFloat + Expr2.Value.vFloat);
            imSub:AOut := NewLiteralExpr(Expr1.Value.vFloat - Expr2.Value.vFloat);
            imMul:AOut := NewLiteralExpr(Expr1.Value.vFloat * Expr2.Value.vFloat);
            imDiv:AOut := NewLiteralExpr(Expr1.Value.vFloat / Expr2.Value.vFloat); // div by zero
            imEqu:AOut := NewLiteralExpr(Expr1.Value.vFloat = Expr2.Value.vFloat);
           imLess:AOut := NewLiteralExpr(Expr1.Value.vFloat < Expr2.Value.vFloat);
             imGr:AOut := NewLiteralExpr(Expr1.Value.vFloat > Expr2.Value.vFloat);
         imNotequ:AOut := NewLiteralExpr(Expr1.Value.vFloat <>Expr2.Value.vFloat);
        imLessEqu:AOut := NewLiteralExpr(Expr1.Value.vFloat <=Expr2.Value.vFloat);
          imGrEqu:AOut := NewLiteralExpr(Expr1.Value.vFloat >=Expr2.Value.vFloat);
         end
   end;
  Result := AOut <> nil;
end;

function TComp.IntConstConv(IntSrc: TExpr;IntDest:TDataType):TExpr;
var
 tmp:TExpr;
begin
   Result := NewConstExpr();
   tmp := NewLiteralExpr(IntSrc.AsInteger);
   if it32Bit in IntDest.BitsClass then
      Result.Value.vUInt := tmp.Value.vUInt
   else if it16Bit  in IntDest.BitsClass then
      Result.Value.vUShort := tmp.Value.vUShort
   else
      Result.Value.vByte := tmp.Value.vByte
end;

function TComp.ConstImplicitConv(Src: TExpr;Dest:TDataType;var AOut:TExpr):boolean;
var
 St:TResBucket;
begin
  AOut:=nil;
  if Src.IsConstant() then
  begin
      if Src.DataType.IsIntType then
           case Dest.TypeClass of
              tcFloat:AOut := NewLiteralExpr(Src.AsNumber);
            tcInteger:AOut := IntConstConv(Src,Dest);
           end
      else if(Dest.TypeClass in [tcInteger,tcChar,tcBool,tcFloat])
           and (Dest.TypeClass = Src.DataType.TypeClass ) then
           begin
              AOut:=NewExpr();
              AOut.Assign(Src);
           end
      else if Src.DataType.IsCharArray and Dest.IsCharArray then
           begin
              St:=TResBucket(Src.Value.vPtr).Clone();
              ffreelist.Add(St);
              St.Size :=TArrayType(Dest).Count;
              AOut:=NewExpr();
              AOut.Assign(Src);
              AOut.Value.vPtr :=St;
              AOut.xOp := imTextStream;
           end
      else if not Src.IsMethod then
           begin
              if CompatibleAssign(Src.DataType, Dest,False) then
              begin
                 AOut:=NewExpr();
                 AOut.Assign(Src);
                 AOut.xOp := Src.xOp;
              end;
           end;
  end else if IsPtrLink(Src) then
  begin
     if CompatibleAssign(Src.DataType, Dest,False) then
     begin
         AOut:=Src;
     end;
  end;
  Result := AOut <> nil;
  if Result then
     AOut.SetDataType(Dest);
end;

function TComp.ConstExplicitConv(Src: TExpr;Dest:TDataType;var AOut:TExpr):boolean;
begin
  AOut:=nil;
  if not ConstImplicitConv(Src,Dest,AOut) then;
    if Src.IsConstant() then
    begin
         if Src.DataType.IsIntType then
            case Dest.TypeClass of // a verifier
                 tcEnum:AOut :=IntConstConv(Src,Dest);
                 tcBool:AOut :=NewLiteralExpr(Src.AsInteger<>0);
                 tcChar:AOut :=NewLiteralExpr(Src.Value.vChar);
              tcPointer:AOut :=NewLiteralExpr(Src.Value.vPtr);
            end
         else if Dest.IsIntType then
            case Src.DataType.TypeClass of
                 tcEnum:AOut :=IntConstConv(Src,Dest);
                 tcBool:AOut :=NewLiteralExpr(integer(Src.AsInteger<>0));
                tcFloat:AOut :=NewLiteralExpr(Src.AsInteger);
                 tcChar:AOut :=NewLiteralExpr(Src.Value.vChar);
              tcPointer:AOut :=NewLiteralExpr(Src.Value.vPtr);
            end;
    end;
  Result := AOut <> nil;
  if Result then
     AOut.SetDataType(Dest);
end;

function TComp.ConstStringOperation(AOp:TQsCmdInst;Expr1, Expr2:TExpr;var AOut:TExpr):boolean;
begin
  AOut:=nil;
    if (AOp =imAdd)and Expr1.IsConstant()and Expr2.IsConstant then
    begin
       if(Expr1.DataType.IsCharArray or (Expr1.DataType.TypeClass=tcChar))
         and (Expr2.DataType.IsCharArray or (Expr2.DataType.TypeClass=tcChar))then
         begin
            AOut := NewLiteralExpr(Expr1.AsString+Expr2.AsString)
         end;
    end;
  Result := AOut <> nil;
end;

function TComp.NewBinBaseExpr(AOp:TQsCmdInst;AExpr1, AExpr2: TExpr): TExpr;
var
 OpType:TDataType;
 CommonType:TDataType;
begin
   if ConstStringOperation(AOp,AExpr1, AExpr2,Result) then
   begin
       Exit;
   end;
   CommonType :=AExpr1.DataType;
   if AExpr2 <> nil then // binary operators
      if not CompatibleType(AExpr1.DataType,AExpr2.DataType,CommonType,AOp) then
         raise ECompException.CreateRes(@UNSUPPORTED_OPERATION);
   OpType := BaseOperationType(AOp,CommonType);
   if OpType = nil  then
      raise ECompException.CreateRes(@UNSUPPORTED_OPERATION);
   RearangeConst(AOp,AExpr1,AExpr2);
   if RelEquConstOptimize(AOp,AExpr1,AExpr2,Result) then
      Exit;
   AExpr1 :=NewImplicitExpr(AExpr1,CommonType);// after this line expr1 & expr2 have same datatype
   if AExpr2 <> nil then // binary operators
   begin
      AExpr2 :=NewImplicitExpr(AExpr2,CommonType);
   end;
   if BaseConstantExprEval(AOp,AExpr1, AExpr2,Result) then
   begin
       Exit;
   end;
   if ArithLogicConstOptimize(AOp,AExpr1, AExpr2,Result) then
      Exit;
   Result := NewExpr(AOp,AExpr1,AExpr2);
   Result.ObjLocation := olTemp;
   Result.SetDataType(OpType);
end;

function TComp.NewBooleanExpr(AOp:TQsCmdInst;AExpr1, AExpr2: TExpr): TExpr;
begin
   AExpr1.ExpectConditionExpr();
   if AExpr2 <> nil then
      AExpr2.ExpectConditionExpr();
   Result := NewBinBaseExpr(AOp,AExpr1,AExpr2);
end;

function TComp.BaseConstantExprEval(AOp:TQsCmdInst;Expr1, Expr2:TExpr;var AOut:TExpr):boolean;
begin
  AOut   := nil;
  Result :=False; // this function uses expr1 & expr2 have same datatype
     case Expr1.DataType.TypeClass of
      tcInteger:Result :=IntExprEval(AOp,Expr1,Expr2,AOut);
         tcBool:Result :=BoolExprEval(AOp,Expr1,Expr2,AOut);
        tcFloat:Result :=FloatExprEval(AOp,Expr1,Expr2,AOut);
         tcEnum:Result :=IntExprEval(AOp,Expr1,Expr2,AOut);
         tcChar:Result :=IntExprEval(AOp,Expr1,Expr2,AOut);
     end;
end;

function TComp.NewBaseIncrExpr(AOp:TQsCmdInst;AExpr,AFactor: TExpr): TExpr;
var
  SizeConst:TExpr;
  Sz:integer;
begin
   AExpr.ExpectLValue();
   if not AFactor.DataType.IsIntType then
      raise ECompException.CreateRes(@INT_TYPE_REQUIRED);
   if (AExpr.DataType.IsOrdinalType() or AExpr.DataType.IsTypedPointer()) then
   begin
      if AExpr.DataType.IsTypedPointer then
        Sz :=AExpr.DataType.Dest.TypeSize
      else
        Sz := 1;
      SizeConst := NewBinBaseExpr(imMul,NewLiteralExpr(Sz),AFactor);
      Result := NewExpr(AOp,AExpr,SizeConst)
   end else
        raise ECompException.CreateRes(@ORDINAL_TYPE_EXPECTED);
end;

function TComp.NewPostIncrExpr(AOp:TQsCmdInst;AExpr:TExpr): TExpr;
begin
   Result := NewBaseIncrExpr(AOp,AExpr,NewLiteralExpr(1));
   Result.SetDataType(AExpr.DataType);
   Result.ObjLocation := olTemp;
end;

function TComp.NewPreIncrExpr(AOp:TQsCmdInst;AExpr,AFactor: TExpr): TExpr;
begin
  Result := NewBaseIncrExpr(AOp,AExpr,AFactor);
  Result.Assign(AExpr);
end;

function TComp.NewPlusExpr(AExpr: TExpr): TExpr;
begin
   if not AExpr.DataType.IsNumericType then
      raise ECompException.CreateRes(@UNSUPPORTED_OPERATION);
   Result :=AExpr;
end;

function TComp.NewAddrExpr(AExpr: TExpr): TExpr;
begin
   if not AExpr.IsAddressable then
      raise ECompException.CreateRes(@ADDRESS_EXPECTED);
   Result := NewExpr(imAddr,AExpr,nil);
   Result.SetDataType(MakePointerType(AExpr.DataType));
   Result.ObjLocation := olTemp;
end;

function TComp.NewDerefExpr(AExpr: TExpr): TExpr;
begin
   if not AExpr.DataType.IsTypedPointer then
      raise ECompException.CreateRes(@TYPED_PTR_EXPECTED);
   Result := NewExpr(imDeref,AExpr,nil);
   Result.SetDataType(AExpr.DataType.Dest);
   Result.ObjLocation:=olMem;
end;

function TComp.BaseDynTypePromotionExpr(AExpr: TExpr): TExpr;
var
  dt:TDataType;
  vTable:TExpr;
  CommonType:TDataType;
begin
   if not AExpr.DataType.IsClass then
      raise ECompException.CreateRes(@UNSUPPORTED_OPERATION);
   NextToken();
   dt := TypeDecl([]);
   if (dt=nil)or not dt.IsClsIntrfType then
      raise ECompException.CreateRes(@REFERENCE_TYPE_EXPEC);

   if dt.IsClass then
   begin
     vTable := MakeAbsolutIndex(TClassStmt(dt.SymbInfo).VTable);
     if not CompatibleType(AExpr.DataType,dt,CommonType,imIs) then
        raise ECompException.CreateRes(@INCOMPATIBLE_TYPE);
   end else begin
      vTable := NewLiteralExpr(TInterfaceType(dt).IID);
   end;
   Result := NewExpr(imNone,AExpr,vTable);
   Result.SetDataType(dt);
   Result.ObjLocation := olTemp;
end;

function TComp.AsExpr(AExpr: TExpr): TExpr;
begin
   Result:= BaseDynTypePromotionExpr(AExpr);
   Result.xOp := imAs;
end;

function TComp.IsExpr(AExpr: TExpr): TExpr;
begin
   Result:= BaseDynTypePromotionExpr(AExpr);
   Result.xOp := imIs;
   Result.ObjLocation := olTemp;
   if Result.DataType.IsClass then
   begin
     if TClassType(AExpr.DataType).IsInstanceOf(Result.DataType) then
     begin
        Result := NewBinBaseExpr(imNotEqu,AExpr,NewLiteralExpr(nil));
        Exit;
     end;
   end;
   Result.SetDataType(BoolType.DataType);
end;

function TComp.__NewNodeTypeConv(AExpr:TExpr;AType:TDataType):TExpr;
begin
   if AExpr.DataType.TypeSize <> AType.TypeSize then
      raise ECompException.CreateRes(@INCOMPATIBLE_TYPE);
   Result := NewExpr(__NodeTypeConvert,AExpr,nil);
   Result.Assign(AExpr);
   Result.SetDataType(AType);
end;
        
function TComp.NewElementAccessExpr(AExpr1, AExpr2: TExpr): TExpr;
var
 idx,v:TExpr;
 Mx,Mn:integer;
 arrType:TArrayType;
begin
   if not AExpr2.DataType.IsOrdinalType()  then
      raise ECompException.CreateRes(@ORDINAL_TYPE_EXPECTED);
   arrType :=TArrayType(AExpr1.DataType);
   if not CompatibleAssign(AExpr2.DataType,arrType.IndexType,False) then
      raise ECompException.CreateRes(@TYPE_ERR);
   Mn :=Trunc(arrType.IndexType.Min_Range);
   Mx :=arrType.Count+Mn -1;
   if AExpr2.IsConstant() then
     if (AExpr2.Value.vInt < Mn)
      or (not arrType.IsOpenArray() and(AExpr2.Value.vInt > Mx)) then
         Msg_Report(msError,LoadResString(@INVALID_INDEX));
   v :=NewBinBaseExpr(imAdd,NewCastExpr(AExpr2,UIntType.DataType),NewLiteralExpr(-Mn));
   idx := NewBinBaseExpr(imMul,v,NewLiteralExpr(AExpr1.DataType.Dest.TypeSize));
   Result :=NewOffsetExpr(AExpr1,idx,arrType.Dest);
end;

function TComp.NewFieldAccessExpr(AExpr1, AExpr2: TExpr): TExpr;
var
  offset:integer;
begin
  offset:=AExpr2.Address;
  Result :=NewOffsetExpr(AExpr1,NewLiteralExpr(offset),AExpr2.DataType);
end;

function TComp.NewOffsetExpr(AExpr1, AExpr2: TExpr;dt:TDataType): TExpr;
var
 Opr:TOprExpr;
 Expr:TExpr;
begin
   if AExpr1.xOp = imOffset then
   begin
      Result :=AExpr1;
      Opr:=TOprExpr(AExpr1);
      Opr.Expr2 :=NewBinBaseExpr(imAdd,Opr.Expr2,AExpr2);
   end else begin
      Expr := AExpr1;
      if Expr.xOp in[imDeref,imRef] then
         AExpr1:=TOprExpr(Expr).Expr1;
      Result := NewExpr(imOffset,AExpr1,AExpr2);
      Result.ObjLocation:=Expr.ObjLocation;
      Result.AccessType := Expr.AccessType;
   end;
   Result.SetDataType(dt);
   Result.Address :=AExpr1.Address;
end;

function TComp.NewMemberExpr(AExpr1: TExpr;AMember:TSymIdent): TExpr;
var
  Expr,Obj,p:TExpr;
begin
   AExpr1.ExpectRValue();
   Expr := MakeAbsolutIndex(AMember);
   if AExpr1.DataType.TypeClass=tcStruct then 
      if not AExpr1.IsAddressable() then     //avoid temp vatiables
         Err(@INSTANCE_EXPECTED);
   if Expr.IsField()and not AExpr1.DataType.IsMetaClass()then
   begin
      if AExpr1.DataType.IsClass() then
      begin
         p :=__NewNodeTypeConv(AExpr1,MakePointerType(AExpr1.DataType));
         AExpr1 := NewDerefExpr(p);
      end;
      Result := NewFieldAccessExpr(AExpr1,Expr)
   end else if Expr.IsClassMethod() then
   begin
      if not AExpr1.DataType.IsMetaClass()then
         raise ECompException.CreateRes(@INSTANCE_MEMBER_EXPECTED);
      Result :=NewExpr(imInstance,AExpr1,Expr); //AExpr1 :vTable
      Result.Assign(Expr);
   end else if Expr.IsMethod() then
   begin
      if AExpr1.DataType.IsMetaClass() then
         raise ECompException.CreateRes(@CLASS_MEMBER_EXPECTED);
      Obj :=AExpr1; // class | struct | interface
      if AExpr1.DataType.TypeClass=tcStruct then
         Obj := NewAddrExpr(AExpr1);
      Result :=NewExpr(imInstance,Obj,Expr);
      Result.Assign(Expr);
   end else begin
      if not AExpr1.DataType.IsMetaClass()then
         raise ECompException.CreateRes(@CLASS_MEMBER_EXPECTED);
      Result := Expr;
   end;
end;

function TComp.NewCastExpr(AExpr: TExpr;Dest:TDataType): TExpr;
begin
   if not CompatibleAssign(AExpr.DataType, Dest,True) then
      raise ECompException.CreateRes(@UNSUPPORTED_OPERATION);
   if AExpr.DataType = Dest then
      Result := AExpr
   else if not ConstExplicitConv(AExpr, Dest,Result) then
   begin
      if AExpr.DataType.IsArray() and Dest.IsArray() then
      begin
          Result :=NewExpr();
          Result.Assign(AExpr);
          Result.SetDataType(Dest);
      end else begin
          Result :=NewExpr(imExplicit,AExpr,nil);
          Result.SetDataType(Dest);
          Result.ObjLocation := olTemp;
      end;
   end;
end;

function TComp.NewImplicitConv(AExpr: TExpr;AType:TDataType): TExpr;
begin
   if not (AExpr.IsCode()and AType.IsFuncType)
      and not CompatibleAssign(AExpr.DataType, AType,False) then
          raise ECompException.CreateRes(@INCOMPATIBLE_TYPE);
   Result := NewImplicitExpr(AExpr,AType);
end;

function TComp.NewAssignExpr(AExpr1, AExpr2: TExpr): TExpr;
begin
   AExpr1.ExpectLValue();
   AExpr2 := NewImplicitConv(AExpr2, AExpr1.DataType);
   Result := NewExpr(imAssign,AExpr1,AExpr2);
   Result.Assign(AExpr1);
end;

function TComp.NewCallExpr(AFuncInf:TExpr;ArgsList:TExprList):TFunctionCallExpr;
var
  I:integer;
  Expr:TExpr;
  FuncEntry,Sym:TSymIdent;
begin
  if not AFuncInf.DataType.IsFuncType then
     raise ECompException.CreateRes(@FUNC_EXPECTED);
  Result := TFunctionCallExpr.Create;
  FfreeList.Add(Result);
  with Result do
  begin
      xOp :=imInvocation;
      if AFuncInf.IsCode then
      begin
        FuncEntry :=TSymIdent(AFuncInf);
        if (AFuncInf.xOp = imInstance)then
        with TOprExpr(AFuncInf) do
          begin
             ObjInstance := Expr1;
             FuncEntry   := TSymIdent(Expr2);
          end;
        if (FuncEntry.Directive = drAbstract)and not (FuncEntry.Parent is TInterfaceStmt) then
           Msg_Report(msWarning,LoadResString(@ABSTRACT_FUNC_CALL),GetLine());
        CheckOverloadFuncCall(FuncEntry ,ArgsList,Sym);
        FuncInst:= MakeAbsolutIndex(Sym);
   //     showmessagefmt('%d',[TFunctype(Sym.DataType).VirtualOffset]);
      end else begin // indirect call from var
        if IsValidFuncCall(AFuncInf.DataType.SymbInfo,ArgsList)=fcNone then
           raise ECompException.CreateRes(@FUNC_CALL_ERROR);
        FuncInst:=AFuncInf;
      end;
      SetDataType(FuncInst.DataType.Dest);
      Result.ObjLocation := olTemp;
      for I:= 0 to ArgsList.Count-1 do
       with TTypeMembers(FuncInst.DataType).Members.GetExpr(I) do
       begin
          Expr := ArgsList.GetExpr(I);
          if QureyKind = atReference then
             ConvArgList.AddExpr(InternalAddr(Expr))
          else
             ConvArgList.AddExpr(NewImplicitExpr(Expr,DataType));
       end;
  end;
end;

function TComp.NewTestExpr(AExpr1, AExpr2, AExpr3: TExpr):TExpr;
var
 CExpr1,CExpr2:TExpr;
 CommonType:TDataType;
begin
   AExpr1.ExpectConditionExpr();
   if not CompatibleType(AExpr2.DataType,AExpr3.DataType,CommonType) then
      raise ECompException.CreateRes(@INVALIDTYPE);
   if AExpr1.IsConstant then
   begin
      Warning_Bool_Eval(AExpr1.Value.vBool);
   end;
   CExpr1 :=NewImplicitExpr(AExpr2,CommonType);
   CExpr2 :=NewImplicitExpr(AExpr3,CommonType);
   Result :=NewExpr(imTest,AExpr1,NewExpr(imNone,CExpr1,CExpr2));
   Result.SetDataType(CommonType);
   Result.ObjLocation := olTemp;
end;

procedure TComp.Warning_Bool_Eval(Value: boolean);
begin
  Msg_Report(msWarning,Format(LoadResString(@WARN_BOOL_EVAL),[BoolToStr(Value)]));
end;

function TComp.NewStmt(QsCmdInst:TQsCmdInst;AClass:TStmtClass):Pointer;
var
 Stmt:TStmt;
begin
   Stmt := AClass.Create;
   Stmt.xOp :=QsCmdInst;
   ffreelist.Add(Stmt);
   Stmt.Line:=GetLine();
   Result:=Stmt;
end;

procedure TComp.ValidateSymbol(ASym:TSymIdent);
begin
  if not FGenereted then
    if not ASym.HasType then
    begin                        // placer en bas des erreurs
       Msg_Report(msError,'forward type '+ASym.Name,ASym.Line or $1000000);
       Exit;
    end;
  if (ASym.ObjLocation = olCode) and (ASym.Value.vPtr= nil)and(ASym.Directive<>drAbstract)  then
    begin                        // placer en bas des erreurs
       Msg_Report(msError,'declaration forward '+ASym.Name,ASym.Line or $1000000);
       Exit;
    end;
  if (ASym.ObjLocation = olLabel)and (TLabelStmt(ASym.Value.vPtr).Stmt= nil)  then
    begin                        // placer en bas des erreurs
       Msg_Report(msError,'declaration forward '+ASym.Name,ASym.Line or $1000000);
       Exit;
    end;
   if  ASym.IsAddressable and (ASym.Visibility=vsPrivate) and not(ASym.ObjLocation in [olParam,olRet])
     and not ASym.Used then
     Msg_Report(msNote,'no used '+ASym.Name,ASym.Line or $1000000);
end;

procedure TComp.ValidateBlock(ABlock:TAllocDeclStmt);
var
 Sym:TSymIdent;
 I:integer;
begin
  for I := 0 to ABlock.Count -1 do // function forward dcl
  begin
      Sym :=ABlock.Symbols[I];
     // showmessage(sym.Name);
      if Sym.IsType()and(Sym.DataType.SymbInfo is TAllocDeclStmt) then
         ValidateBlock(TAllocDeclStmt(Sym.DataType.SymbInfo)) ;
     // else if (Sym.TypeConstructor)and(Sym.DataType.SymbInfo is TAllocDeclStmt) then
      //   ValidateBlock(TAllocDeclStmt(Sym.DataType.SymbInfo));
      ValidateSymbol(Sym)
  end;
end;

procedure TComp.ValidateGlobalBlock();
var
 Sym:TExpr;
 I:integer;
begin
 for I := 0 to FUnit.Count -1 do // function forward dcl
 begin
      Sym :=FUnit.Symbols[I];
      if Sym.IsType()then
      begin
         if Sym.DataType.SymbInfo is TAllocDeclStmt then
            ValidateBlock(TAllocDeclStmt(Sym.DataType.SymbInfo));
         ValidateSymbol(TSymIdent(Sym));
      end;
 end;
 with TTypeMembers(FUnit.DataType).Members do
  for I:=0 to Count-1 do
  begin
      Sym :=GetExpr(I);
      if Sym.IsType()and(Sym.DataType.SymbInfo is TAllocDeclStmt) then
         ValidateBlock(TAllocDeclStmt(Sym.DataType.SymbInfo));
      ValidateSymbol(TSymIdent(Sym))
  end;
end;

procedure TComp.StartDecls;
var
  Obj:TSymIdent;
begin
    if not SameText(Name ,'system')then // includes system unit on the uses
       FMainComp.LoadUnit('system',FUnit);
    FStacks.Push(FUnit.CodeList,[ssActiveCodeStmt]);
    FUnit.DefaultVarClass :=olStatic;
    EnterScope(FUnit,[ssConstsList,ssNamesList,ssAlloc,ssFuncList]);
    CompileSection();
    ExitScope();
    FStacks.Pop;
    FMainComp._CompList.Add(Self);
    if FGenereted then
       Exit
    else
       ValidateGlobalBlock();

    if ErrorsCount>0 then
       Exit;
    FGenerator.CodeGen(AList);
    FGenerator.MakeObj();
    if SameText(Name,'system') then
    begin
        if not FUnit.FindMember('object',Obj)// object definition
           or not Obj.IsType or not Obj.DataType.IsClass then
              Err(@OBJECT_DEF_ERROR);
        FMainComp.ObjectClass := TClassStmt(Obj.DataType.SymbInfo);
    end;
end;

function TComp.NewSymbol(const AName:string;ASection:TListKind;AModifiers:TDclModifiers;dt:TDataType):TSymIdent;
begin
   Result:= NameStacks[ASection].NewSymbol(AName,TSymIdent);
   SetSymProps(Result,AName,AModifiers,dt);
end;

procedure TComp.SetSymProps(ASym:TSymIdent;const AName:string;AModifiers:TDclModifiers;dt:TDataType);
begin
   ASym.SetDataType(dt);
   ASym.xOp := imSymb;
   ASym.BaseUnit :=FUnit;
   ASym.Name := AName;
   ASym.Line := GetLine();
   ASym.SetModifiers(AModifiers);
   if dmReadonly in AModifiers then
      ASym.AccessType := qoReadOnly;
end;

procedure TComp.ModifiersCheck(AModifiers,sTest:TDclModifiers);
begin
   if (AModifiers - sTest)<>[] then
       Err(@INVALID_MODIFIER);
end;

function TComp.CreateTypeInfo():TDataType;
var
  Sym:TExpr;
begin
   Result := nil;
   case CurrentToken of
      uuChar: Result := CharType.DataType;
     uuShort: Result := ShortType.DataType;
    uuUshort: Result := UShortType.DataType;
       uuInt: Result := IntType.DataType;
      uuUint: Result := UIntType.DataType;
      uuVoid: Result := VoidType.DataType;
     uuSbyte: Result := SByteType.DataType;
      uuByte: Result := ByteType.DataType;
     uuFloat: Result := FloatType.DataType;
      uuBool: Result := BoolType.DataType;
     uuStruct,uuUnion,uuClass,uuInterface,
       uuEnum,uuEvent: Result :=  ExtentedType_Dcl();
     uuIdent:if GetID(GetTokenTxt(),Sym,True,True) then
             begin
               if Sym.ObjLocation =olType then
                  Result := Sym.DataType;
             end;
   end;
   if Result = nil then
      Err(@TYPE_REQUIRED);
   NextToken();
end;

procedure TComp.Var_Dcl(AModifiers:TDclModifiers);
var
  dt,ds:TDatatype;
  varname:string;
  Sc:TAllocDeclStmt;
  vVar:TSymbolExpr;
  bf:TBitField;
  isUnamed:boolean;
  DynStmt:TStmt;
begin
   dt:=TypeDecl(AModifiers+[dmOpenArray,dmTypeRequired]); // open array in dcls
   Sc := NameStacks[ssAlloc];
   vVar   := nil;
   isUnamed :=False;
   repeat
      ds :=dt;
      if CurrentToken = uuIdent then
      begin
          varname := GetTokenTxt();
          vVar:=NewSymbol(varname,ssNamesList,AModifiers,dt);
          NextToken;
      end else begin
        if not (dmAbstractDcl in AModifiers) then
           CheckCurrentToken(uuIdent);
        if vVar <> nil then // only one item
           Msg_Report(msError,@INSTSEP_EXPECTED);
        vVar:= NameStacks[ssNamesList].NewSymbol(TSymIdent);
        vVar.SetDataType(dt);
        isUnamed :=True;
      end;
      if (dmStatic in AModifiers)or(dmReadonly in AModifiers) then
         AllocateStatic(vVar)
      else if dmAuto in AModifiers then
         AllocateLocal(vVar)
      else
         Sc.Allocate(vVar);
      if (dmBitField in AModifiers)and TryCurrentToken(uuDef) then  // bits Field
      begin
        CheckCurrentToken(uuIntNumber);
        bf := MakeBitFieldType(dt,StrToInt(GetTokenTxt()));
        ds :=bf;
        NextToken;
      end;
      vVar.DataType:=ds;
      if (dmReadonly in AModifiers)
         or ((CurrentToken=uuOpAssign)and(dmInitializer in AModifiers)) then
      begin
        CheckCurrentAndMove(uuOpAssign);
        if (dmStatic in AModifiers)or(dmReadonly in AModifiers) then
        begin
            vVar.Value.vPtr:= NewInitializer(ds,True);
        end else begin
            DynStmt := NewLocalInitializer(vVar);
            GetActiveCodeStmt().List.Add(DynStmt);
        end;
      end;
      if dt.IsOpenArray() then
         Msg_Report(msError,@CONSTANT_EXPR_EXPECED);
      if CurrentToken=uuIdent then
         Msg_Report(msError,@SEPARATOR_EXPECTED)
      else begin
          if CurrentToken<>uuSep then
             break;
          NextToken;
      end;
      if isUnamed then
           break;
   until False;
   CheckCurrentToken(uuInstSep);
end;

procedure TComp.Const_Stmt(AModifiers:TDclModifiers);
var
  constname:string;
  vConst:TSymbolExpr;
  C:TExpr;
begin
   ModifiersCheck(AModifiers,[dmPrivate,dmPublic]);
   NextToken;
   while CurrentToken = uuIdent do
   begin
      constname := GetTokenTxt();
      vConst:=NewSymbol(constname,ssConstsList,AModifiers,nil); //op dt type
      vConst.ObjLocation:=olLiteral;
      GetNextTokenAndCheck(uuopAssign);
      NextToken;
      C :=ExpectConstantExpr();
      vConst.Value^ :=C.Value^;
      if C.xOp = imTextStream then
         vConst.xOp :=imTextStream;
      vConst.SetDataType(C.DataType); //opt  for type
      if CurrentToken=uuIdent then
         Msg_Report(msError,@SEPARATOR_EXPECTED)
      else begin
          if CurrentToken<>uuSep then
             break;
          NextToken;
      end;
   end;
   CheckCurrentToken(uuInstSep);
end;

function TComp.IsTypeSpecifier(AExtraDcl:boolean):boolean;
var
  Sym:TExpr;
begin
  Result :=(CurrentToken in [ uuInt, uuShort, uuSbyte ,
                              uuUint,uuUshort,uuByte,
                              uuChar,uuVoid,uuBool,uuFloat]);
  if Result then
     Exit;
  if CurrentToken = uuIdent then
  begin
      Push();
      if GetID(GetTokenTxt(),Sym,True,False)then
         Result := Sym.ObjLocation =olType;
      Pop(False);
  end;
  if Result or not AExtraDcl then
     Exit;
  Result :=  CurrentToken in [uuClass,uuStruct,uuUnion,uuEnum,uuInterface];
end;

function TComp.MetaClass():TDataType;
begin
    NextToken();
    Result := TypeDecl([]);
    if (Result=nil)or not Result.IsClass  then
      raise ECompException.CreateRes(@CLASS_TYPE_EXPECTD);
    Result := MakeMetaClassType(TClassType(Result));
end;

function TComp.TypeDecl(AModifiers:TDclModifiers):TDataType;
var
 Ptrdepth:integer;
 isVoidType:boolean;
 vType:TSymIdent;
 s:string;
 function RightToLeftArrDcl(ADestType:TDataType):TArrayType;
 var
   IdxType:TDataType;
   Len:TExpr;
 begin
     NextToken();
     if IsTypeSpecifier(False) then
     begin
       IdxType := CreateTypeInfo();
       if not IdxType.IsOrdinalType then
          Err(@ORDINAL_TYPE_EXPECTED);
       if IdxType.TypeClass =tcEnum then
          Len:= NewLiteralExpr(TTypeMembers(IdxType).Members.Count)
       else
          Len:= NewLiteralExpr(integer(Round(IdxType.Max_Range-IdxType.Min_Range))+1);
     end else begin
       Len := Expression(False,False);
       if Len <> nil then
       begin
         if not Len.IsConstant() then
            Msg_Report(msError,@CONSTANT_EXPR_EXPECED);
         if (not Len.DataType.IsIntType)or(Len.Value.vInt<= 0) then
            Err(@INT_TYPE_REQUIRED);
       end else begin
         if not(dmOpenArray in AModifiers )  then
            Msg_Report(msError,@CONSTANT_EXPR_EXPECED);
         Len:= NewLiteralExpr(0);
       end;
       IdxType :=UintType.DataType;
     end;
     CheckCurrentAndMove(uuIdxR);
     if CurrentToken=uuIdxL then
         ADestType:= RightToLeftArrDcl(ADestType);
     Result:= MakeArrayType(ADestType,Len.Value.vInt,IdxType)
 end;
begin
     isVoidType := CurrentToken = uuVoid ;
     Result := nil;
     if IsTypeSpecifier(False) then
     begin
        Result := CreateTypeInfo();
     end else if(dmExtentedType in AModifiers) then
     begin
        Result := ExtentedType_Dcl();
        if Result <> nil then
           NextToken();
     end;
     Ptrdepth:=0;
     if Result = nil then
     begin
          if CurrentToken = uuRef then
             Result := MetaClass()
          else if CurrentToken = uuIdent then
          begin
              Push();  // forward ptr
              s:=GetTokenTxt;
              if (NextToken=uuOpStar) and(NextToken=uuInstSep) then
              begin
                  vType :=NewSymbol(s,ssNamesList,AModifiers,nil);
                  vType.ObjLocation :=olType;
                  Result := MakePointerType(VoidType.DataType);
                  TSymIdent(Result.SymbInfo).Visibility := vType.Visibility;
                  vType.Value.vPtr := Result;
              end;
              Pop(Result<>nil);
          end;
     end else begin
           if (dmPtrDcl in AModifiers)and TryCurrentToken(uuOpStar)then //pointer
           begin //only one pointer
              Result := MakePointerType(Result);
              inc(Ptrdepth);
           end else if (Result <> nil)and(dmArrayDcl in AModifiers) then
             if CurrentToken=uuIdxL then //array
             begin
                Result:= RightToLeftArrDcl(Result);
             end;
     end;
     if (dmTypeRequired in AModifiers)and(Result = nil)then
        Err(@TYPE_REQUIRED);
     if isVoidType and(Ptrdepth = 0)
        and not (dmVoidDcl in AModifiers) then  //void type bad usage
        Err(@INVALID_VOID_USAGE);
end;

procedure TComp.Var_Stmt(AModifiers:TDclModifiers);
begin
    NextToken;
    Var_Dcl(AModifiers+[dmPtrDcl,dmArrayDcl,dmExtentedType,dmInitializer]);
end;

function TComp.ExtentedType_Dcl():TDatatype;
begin
   Result := nil;
   case CurrentToken of
    uuStruct:Result := Struct_Stmt().DataType;
     uuUnion:Result := Struct_Stmt().DataType;
      uuEnum:Result := Enum_Stmt().DataType;
     uuEvent:Result := Event_Stmt([]);
   end;
end;

procedure TComp.Type_Stmt(AModifiers:TDclModifiers);
var
   dt:TDatatype;
   typename:string;
   vType,pSrc:TSymIdent;
begin
    ModifiersCheck(AModifiers,[dmPrivate,dmPublic,dmExtentedType,dmPtrDcl,dmArrayDcl]);
    NextToken;
    CheckCurrentToken(uuIdent);
    typename := GetTokenTxt();
    if NameStacks[ssNamesList].FindMember(typename,vType) then
    begin
       if vType.HasType()then
          raise ECompException.CreateFmt(LoadResString(@TYPE_NAME_EXPECTED)+' "%s"',[typename]);
    end else begin
       vType :=NewSymbol(typename,ssNamesList,AModifiers,nil);
       vType.ObjLocation :=olType;
    end;
    GetNextTokenAndCheck(uuopAssign);
    NextToken;
    dt := nil;
    if dmExtentedType in AModifiers then
       case CurrentToken of
            uuClass:dt := Class_Stmt(vType).DataType;
        uuInterface:dt := Interface_Stmt(vType).DataType;
        else
          dt := ExtentedType_Dcl();
        end;
    if dt = nil then
    begin
       dt:=TypeDecl(AModifiers+[dmTypeRequired]);
       CheckCurrentToken(uuInstSep);
    end;
    vType.SetDataType(dt);
    if vType.Value.vPtr <> nil then
    begin
       pSrc := TSymIdent(TDatatype(vType.Value.vPtr).SymbInfo);
       if vType.Visibility<> pSrc.Visibility then   // dcl not in same section
         raise ECompException.CreateRes(@INVALIDTYPE);
       TDatatype(vType.Value.vPtr).Dest :=dt;
       vType.Value.vPtr:=nil;
    end;
end;

function TComp.Struct_Stmt():TStructStmt;
begin
  if CurrentToken = uuUnion then
     Result:=NewScope(TUnionStmt)
  else
     Result:=NewScope(TStructStmt);
  Result.DefaultVarClass := olField;
  NextToken;
  CheckCurrentToken(uuBrassL);
//  FStacks.Push(nil,[ssCodeBlock]); avoid auto var decl
  EnterScope(Result,STRUCT_LISTS);
  repeat
      NextToken();
      case CurrentToken of
           uuConst:Const_Stmt([dmPublic]);
          uuStatic:Var_Stmt([dmStatic,dmInitializer]);
        uuReadonly:Var_Stmt([dmStatic,dmReadonly]);
            uuType:Type_Stmt([dmExtentedType,dmPtrDcl,dmArrayDcl]);
         uuStruct,
           uuUnion,uuEvent,
            uuEnum:Var_Dcl([dmExtentedType,dmPtrDcl,dmArrayDcl]) { }
      else if IsTypeSpecifier() then // a completer
              Var_Dcl([dmPtrDcl,dmArrayDcl,dmBitField])
           else
              break;
      end;
  until False;
  Result.Validate();
  while CurrentToken = uuFunc do
  begin
     Func_Stmt([]);// dmFuncForward
     NextToken();
  end;
  CheckCurrentToken(uuBrassR);
  ExitScope();
 // FStacks.Pop();
end;

function TComp.Class_Stmt(ATypeName:TSymIdent):TClassStmt;
var
 Mds:TDclModifiers;
 ParCls:TDataType;
begin
  Result:=NewScope(TClassStmt);
  ATypeName.SetDataType(Result.DataType);
  Result.Name := ATypeName.Name;
  Result.DefaultVarClass := olField;
  Result.Ancestor := FMainComp.ObjectClass;
  Result.WriteInternalSymboles();
  AllocateStatic(Result.VTable);
  AllocateStatic(Result.IntrfsTable);
  if NextToken=uuDef then
  begin
    NextToken;
   // CheckCurrentToken(uuIdent);
    ParCls := TypeDecl([dmTypeRequired]);
    if ParCls.IsClass then
       Result.Ancestor :=TClassStmt(ParCls.SymbInfo)
    else if ParCls.IsInterface() then
       Result.AddInterface(ParCls)
    else
       Err(@CLASS_TYPE_EXPECTD);
    while CurrentToken = uuSep do
    begin
       NextToken();
       ParCls := TypeDecl([dmTypeRequired]);
       if not ParCls.IsInterface then
          Err(@INTERFACE_TYPE_EXPECTD);
       Result.AddInterface(ParCls);
    end;
  end;
  CheckCurrentToken(uuBrassL);

 // FStacks.Push(nil,[ssCodeBlock]);
  EnterScope(Result,STRUCT_LISTS);
  repeat
      Mds:=GetModifiers();
      case CurrentToken of
           uuConst:Const_Stmt(Mds);
        uuReadonly:Var_Stmt(Mds+[dmStatic,dmReadonly]);
            uuType:Type_Stmt(Mds+[dmExtentedType,dmPtrDcl,dmArrayDcl]);
            uuEnum:Var_Dcl(Mds+[dmExtentedType,dmPtrDcl,dmArrayDcl]) { }
      else if IsTypeSpecifier() then
              if dmStatic in Mds then //static var
                 Var_Dcl(Mds+[dmPtrDcl,dmArrayDcl,dmExtentedType,dmInitializer])
              else // field
                 Var_Dcl(Mds+[dmPtrDcl,dmArrayDcl])
           else
              break;
      end;
  until False;
  Result.Validate();
  while CurrentToken = uuFunc do
  begin
     Func_Stmt(Mds);// dmFuncForward
     Mds:=GetModifiers();
  end;
  BuildClassTable(Result);
  CheckCurrentToken(uuBrassR);
  ExitScope();
 // FStacks.Pop();
end;

function TComp.NewStaticAddr(ASym:TSymIdent):TExpr;
begin
    Result := MakeAbsolutIndex(ASym);
    Result := NewAddrExpr(Result);
end;

function TComp.NewInt32(AValue:integer):TExpr;
begin
     ConstImplicitConv(NewLiteralExpr(AValue),IntType.DataType,Result);
end;

function TComp.PutInternalSymbol(AClass:TClassStmt;AList:TInitializerExpr):TSymIdent;
var
  AType :TDataType;
  ALen:integer;
begin
    Result := AClass.NewSymbol(TSymIdent);
    ALen := AList.Elements.Count;
    AType := MakeArrayType(PtrType.DataType,ALen,uIntType.DataType);
    Result.SetDataType(AType);
    Result.Used :=True;
    Result.Visibility :=vsPublic;
    AllocateStatic(Result);
    Result.Value.vPtr:=AList;
end;

function TComp._CreateClassVirtualTable(AClass:TClassStmt):TSymIdent;
var
 I:integer;
 Vecc:TExpr;
 List:TInitializerExpr;
begin
    List:=NewInitializerListExpr();
    if AClass.Ancestor <> nil then
    begin
       List.Elements.AddExpr(NewStaticAddr(AClass.Ancestor.VTable))// parent
    end else begin
       List.Elements.AddExpr(NewLiteralExpr(nil));
    end;
    List.Elements.AddExpr(NewStaticAddr(AClass.IntrfsTable)); //intfTable
    List.Elements.AddExpr(NewInt32(TClassType(AClass.DataType).Instance_Size));// instancesize
    if AClass.VirtualMembers.Count = 0 then
       List.Elements.AddExpr(NewLiteralExpr(nil))
    else
      for I := 0 to AClass.VirtualMembers.Count -1do // fill class vtable
      begin
          Vecc := NewStaticAddr(TSymIdent(AClass.VirtualMembers[I]));
          List.Elements.AddExpr(Vecc);
      end;
    Result := PutInternalSymbol(AClass,List);
end;

function TComp._CreateIntfFuncsTable(AClass:TClassStmt;ATable:TIntrfImplementation):TSymIdent;
var
 FuncsTable:TInitializerExpr;
 procedure ProcessIntrf(AIntrf: TInterfaceStmt);
 var
   I:integer;
   Vecc:TExpr;
   B:TSymIdent;
 begin
    if AIntrf.Ancestor <> nil then
       ProcessIntrf(AIntrf.Ancestor);
    with AClass.IntrfsTables.GetIntrf(AIntrf.DataType) do
      for I := 0 to Table.Count-1 do
      begin
          B :=Table[I];
          Vecc := NewStaticAddr(B);
          FuncsTable.Elements.AddExpr(Vecc);
      end;
 end;
begin
    FuncsTable:=NewInitializerListExpr();
    ProcessIntrf(ATable.MType);
    Result :=PutInternalSymbol(AClass,FuncsTable);
end;

function TComp._CreateIntrfVTable(AClass:TClassStmt):TSymIdent;
var
 I:integer;
 _IID:integer;
 EntryList:TInitializerExpr;
 mTable:TIntrfImplementation;
 B:TSymIdent;
begin
    EntryList:=NewInitializerListExpr();
    EntryList.Elements.AddExpr(NewInt32(AClass.FUsedIntrfs.Count));// interfaces count ;
    with AClass do
      for I := 0 to FUsedIntrfs.Count-1 do
      begin
          mTable := FUsedIntrfs.GetItem(I);
          _IID := TInterfaceType(mTable.DataType).IID;
          B := _CreateIntfFuncsTable(AClass,mTable);
          EntryList.Elements.AddExpr(NewStaticAddr(B));
          EntryList.Elements.AddExpr(NewInt32(_IID));
          EntryList.Elements.AddExpr(NewInt32(mTable.Address));
      end;
    Result := PutInternalSymbol(AClass,EntryList);
end;

procedure TComp.BuildClassTable(AClass:TClassStmt);
var
 I,J,VIdx:integer;
 B,Bind:TSymIdent;
 BindError:boolean;
 Base:TExpr;Expr:TExpr;
 Impl:TIntrfImplementation;
begin
  with AClass do
  begin
    for I := 0 to Count -1 do
    begin
        B := Symbols[I];
        repeat
            if B.Directive in [drVirtual,drAbstract] then
            begin
               TFuncType(B.DataType).VirtualOffset:=VirtualMembers.Count;
               VirtualMembers.Add(B);
            end else if B.Directive = drOverride then
            begin
               Base:= FindOverloadFunc(B.Name,AClass.Ancestor,TFuncType(B.DataType),True);
               VIdx :=TFuncType(Base.DataType).VirtualOffset;
               VirtualMembers[VIdx]:=B;
               TFuncType(B.DataType).VirtualOffset:=VIdx;
            end;
            B := B.NextSym;
        until B =nil;
    end;
    BindError := false;
    for I := 0 to IntrfsTables.Count-1 do
    begin
        Impl := IntrfsTables.GetItem(I);
        with TInterfaceType(Impl.MType.DataType).Members  do
          for J := 0 to Count-1 do
          begin
              Bind := Impl.Table[J];     // instance
              B := TSymIdent(GetExpr(J));//symb from intrface
              if Bind = nil then
                 Bind:= FindOverloadFunc(B.Name,AClass,TFuncType(B.DataType),False);
              if Bind<>nil then
              begin
                 if Bind.IsVirtualFunc then
                    Msg_Report(msError,LoadResString(@BIND_INTRF_VIRT_ERR),Bind.Line);
                 Impl.Table[J]:=Bind;
              end else begin
                 BindError := True;
                 Msg_Report(msError,Format('bind "%s"',[B.Name]))
              end;
          end;
    end;
    if BindError then
       Err(@BIND_INTRF_ERR);
    B := _CreateIntrfVTable(AClass);
    IntrfsTable.Value.vPtr := NewStaticAddr(B);
    //Virtual methods table -
    B := _CreateClassVirtualTable(AClass);
    Expr :=  NewElementAccessExpr(MakeAbsolutIndex(B),NewLiteralExpr(3));
    VTable.Value.vPtr := NewAddrExpr(Expr);
  end;
end;

function TComp.Interface_Stmt(ATypeName:TSymIdent):TInterfaceStmt;
var
 ParInterface:TDataType;
begin
  Result:=NewScope(TInterfaceStmt);
  ATypeName.SetDataType(Result.DataType);
  Result.Name := ATypeName.Name;
 // Result.DefaultVarClass := olField;
  if NextToken=uuDef then
  begin
    NextToken;
    CheckCurrentToken(uuIdent);
    ParInterface := TypeDecl([dmTypeRequired]);
    if not ParInterface.IsInterface() then
       Err(@INTERFACE_TYPE_EXPECTD);
    Result.Ancestor :=TInterfaceStmt(ParInterface.SymbInfo);
  end;
  if CurrentToken=uuIntNumber then
  begin
    TInterfaceType(Result.DataType).IID := StrToInt(GetTokenTxt);
    NextToken;
  end;
  CheckCurrentToken(uuBrassL);
  EnterScope(Result,STRUCT_LISTS);// a verifier
  while NextToken = uuFunc do
  begin
     Func_Stmt([dmAbstract,dmFuncForward]);
  end;
  Result.Validate();
  CheckCurrentToken(uuBrassR);
  ExitScope();
end;

function TComp.Enum_Stmt():TAllocDeclStmt;
var
  tp:TDataType;
  vEnumConst:TSymbolExpr;
  vName:string;
  EnumVal,MnSize,MxSize,vSize:integer;
  vValue:TExpr;
  Signed:boolean;
begin
    tp:=nil;
    if NextToken=uuDef then
    begin
      NextToken;
      tp :=TypeDecl([dmTypeRequired]);
      if not tp.IsIntType then
         Err(@INT_TYPE_REQUIRED);
    end;
    Result := NewScope(TEnumStmt);
    CheckCurrentToken(uuBrassL);
    EnterScope(Result,[]);//ssConstsList
    EnumVal:=-1;
    MnSize := 0;
    MxSize := 0;
    vSize  := 0;
    Signed := False;
    repeat
       try
           NextToken();
           CheckCurrentToken(uuIdent);
           vName:=GetTokenTxt();
           vEnumConst:=NewSymbol(vName,ssConstsList,[dmPublic],Result.DataType);
           vEnumConst.ObjLocation:=olLiteral;
           Result.Allocate(vEnumConst);
           if NextToken()=uuOpAssign then
           begin
               NextToken();
               vValue :=ExpectConstantExpr();
               if not vValue.DataType.IsIntType then
                  Err(@INT_TYPE_REQUIRED);
               EnumVal := vValue.Value.vInt;
           end else begin
               Inc(EnumVal);
           end;
           if EnumVal<MnSize then
              MnSize:=EnumVal;
           if EnumVal>MxSize then
              MxSize:=EnumVal;
           vSize := ValueSize(MnSize,MxSize,Signed);
           vEnumConst.Value.vInt := EnumVal;
       except on e:ECompException do
          begin
             Msg_Report(msError,e.Message);
             ErrorSync();
          end;
       end;
       if CurrentToken=uuIdent then
          Msg_Report(msError,ExpectToken(uuSep))
       else if CurrentToken<>uuSep then
          break;
    until False;
    CheckCurrentToken(uuBrassR);
    if tp <> nil then
    begin
       if (MnSize<tp.Min_Range)or(MxSize>tp.Max_Range) then
           Err(@TYPE_OVERFLOW);
    end else begin
       tp:= MakeIntType(vSize,Signed).DataType;
    end;
    TENumStmt(Result).SetTypeBase(tp);
    ExitScope();
end;

function TComp.Event_Stmt(AModifiers:TDclModifiers):TDatatype;
var
  tp:TDataType;
begin
  ModifiersCheck(AModifiers,[dmStatic]);
  CheckCurrentAndMove(uuEvent);
  if CurrentToken = uuStatic then
  begin
     AModifiers:=AModifiers+[dmStatic];
     Nexttoken();
  end;
  tp :=TypeDecl([dmVoidDcl,dmPtrDcl,dmTypeRequired]);
  Result :=ArgsListDcl(tp,[dmAbstractDcl]+AModifiers).DataType;
end;

function TComp.FindOverloadFunc(const AName:string;AScope:TScope;AFunc:TFuncType;AMustExists:boolean):TSymIdent;
var
  Startscope:TScope;
begin
   Startscope:=AScope;
   FSymSearch.Text := AName;
   repeat
       if AScope.FindMember(FSymSearch,Startscope)
          and FSymSearch.Mutch.FindSignature(AFunc,Result)
          and AFunc.IsEqual(Result.DataType) then
              Exit;
       if not (AScope is TClassStmt) then
          break;
       AScope := TClassStmt(AScope).Ancestor;
   until AScope=nil;
   Result := nil;
   if AMustExists then
      Err(@FUNC_SIGNATURE_ERR);
end;

function TComp.GetFuncSignature(AEntry:TSymIdent;AFunc:TFuncType;AMustExists:boolean):TSymIdent;
var
  AClass:TInheritedType;
begin
   repeat
       if AEntry.FindSignature(AFunc,Result) then
       begin
         if AMustExists and not AFunc.IsEqual(Result.DataType) then
             Err(@FUNC_SIGNATURE_ERR);
         Exit;
       end;
       if not(AEntry.Parent is TInheritedType)then
          break;
       FSymSearch.Text := AEntry.Name;
       AClass :=AEntry.Parent as TInheritedType;
       if not AClass.FindInheritedMember(FSymSearch) then
          break;
       AEntry := FSymSearch.Mutch;
   until False;
   if AMustExists then
      Err(@FUNC_SIGNATURE_ERR);
end;

function TComp.ArgsListDcl(ADest:TDataType;AModifiers:TDclModifiers):TAllocDeclStmt;
var
  tp:TDataType;
  vParam:string;
  vId:TSymbolExpr;
  Sc:TAllocDeclStmt;
  Initialize:boolean;
  byRef:boolean;
  Func:TFuncType;
begin
    if ADest.IsStructArrayType then
       Err(@INVALIDTYPE);
    Result := NewScope(TFuncHeaderStmt);
    Result.DataType.Dest :=ADest;
    Result.SetModifiers(AModifiers);
    if not(dmStatic in AModifiers) then
    begin
       Func := TFuncType(Result.DataType);
       Func.FuncKind := mkMethod;
       if dmClassMthd in AModifiers then
          Func.FuncKind := mkClassMethod;
       Func.TypeSize := SIZEOFPOINTER * 2;
    end;
    Result.DefaultVarClass :=olParam;
    CheckCurrentAndMove(uuExprL);
    EnterScope(Result,[ssNamesList]);
    tp := TypeDecl([dmOpenArray,dmPtrDcl,dmArrayDcl]);
    Sc := NameStacks[ssNamesList];
    Initialize:=False;
    if tp <> nil then
      repeat
         byRef := CurrentToken=uuOpAnd;
         if byRef then
            NextToken();
         if dmAbstractDcl in AModifiers then
         begin
            vId:=Sc.NewSymbol(TSymIdent);
            vId.SetDataType(tp);
         end else begin
            CheckCurrentToken(uuIdent);
            vParam:=GetTokenTxt();
            vId:=NewSymbol(vParam,ssNamesList,[],tp);
            NextToken();
            if CurrentToken =uuopAssign then
               Initialize :=True;
         end;
         Sc.Allocate(vId);
         if byRef or(vId.DataType.IsStructArrayType) then
         begin
           if Initialize then
              Msg_Report(msError,@INIT_REF_ERROR);
           vId.QureyKind := atReference;
         end else if Initialize then
         begin
            NextToken();
            vId.Value.vPtr := ExpectConstantExpr(); // default value
         end;
         if CurrentToken <> uuSep then
            break;
         NextToken;
         tp :=TypeDecl([dmTypeRequired,dmOpenArray,dmPtrDcl,dmArrayDcl]);
      until False;
    CheckCurrentToken(uuExprR);
    ExitScope();
end;

function TComp.FunctionBlock(AFunc:TSymIdent):TBlockStmt;
var
 BlockInf:TFuncBlockStmt;
 MethodType:TDataType;
begin
    BlockInf:=NewScope(TFuncBlockStmt);
    BlockInf.DefaultVarClass := olAuto;
    BlockInf.Header:= AFunc;
    if AFunc.IsMethod() then
    begin
       MethodType := GetActiveObject().DataType;
       if MethodType.TypeClass =tcStruct then
          BlockInf.SelfExpr.QureyKind := atReference;
       if AFunc.IsClassMethod then
          MethodType:= MakeMetaClassType(TClassType(MethodType));
        BlockInf.SelfExpr.SetDataType(MethodType);
    end;
    FActiveFunc := BlockInf;
    Result := NewStmt(imBlockStmt,TBlockStmt);
    Result.Graphs :=TGraphSection.Create;
    FfreeList.Add(Result.Graphs);
    BlockInf.Code := Result;
    AFunc.Value.vPtr := Result;
    CheckCurrentToken(uuBrassL);
    EnterScope(BlockInf,[ssConstsList,ssNamesList,ssAlloc]);
    Result.S:= StmtList();
    CheckCurrentToken(uuBrassR);
    BlockInf.Epilogue:= NewStmt(imFuncEpilogue,TStmt);
    ExitScope();
    FActiveFunc := nil;
    FUnit.FuncList.Add(BlockInf);
    ValidateBlock(BlockInf);
end;

function TComp.InterfaceFuncSelector():TIntrfImplementation;
var
  vClass:TClassStmt;
  tp:TDataType;
begin
    Result := nil;
    if CurrentToken <> uuIdent then
       Exit;
    tp := nil;
    Push();
    FSymSearch.Text :=GetTokenTxt();
    if NameStacks[ssNamesList].Find(FSymSearch)
       and FSymSearch.Mutch.DataType.IsInterface then
           tp := FSymSearch.Mutch.DataType;
    Pop(tp <> nil);
    if tp = nil then
       Exit;
    vClass:= TClassStmt(FStacks[ssFuncList]);
    Result := vClass.IntrfsTables.GetIntrf(tp);
    NextToken();
end;

function TComp.AbsoluteFuncSelector(AModifiers:TDclModifiers):TFuncHeaderInf;
var
  tp:TTypeMembers;
  Ret:TSymIdent;
  LongPath:boolean;
  Scope:TAllocDeclStmt;
begin
    Result.Exists :=False;
    Scope  := TAllocDeclStmt(FStacks[ssFuncList]);
    LongPath:= Scope=FUnit;
    repeat
       Result.Header := nil;
       CheckCurrentToken(uuIdent);
       Result._Name := GetTokenTxt();
       NextToken;
       if not Scope.FindMember(Result._Name,Ret) then
          break;
       Result.Header  := Ret;
       if (CurrentToken <> uuOpDot)or (not LongPath) then
          break;
       if(Ret.DataType.SymbInfo is TFieldType) then
       begin
          tp := TTypeMembers(Ret.DataType);
          Scope:= TFieldType(tp.SymbInfo);
       end else
             Err(@SCOPE_EXPECTED);
       FStacks.Push(Scope,STRUCT_LISTS);
       NextToken;
    until False;
    Result.Exists := Result.Header <> nil;
end;

procedure TComp.Check_Class_Symbol(AMember:TSymIdent;AImpl:TIntrfImplementation;AClass:TClassStmt);
var
  Entry,BaseEntry:TSymIdent;
begin
  if AImpl <> nil then
     if not AClass.UpdateIntrfFuncEntry(AImpl,AMember)then
        Msg_Report(msError,Format('bind "%s"',[AMember.Name]));
   FSymSearch.Text :=AMember.Name;
   Entry := nil;
   if AClass.FindInheritedMember(FSymSearch) then
      Entry := FSymSearch.Mutch;
   with AMember do
   begin
     if Entry = nil then
     begin
        if Directive= drOverride then
           raise ECompException.Createfmt('member "%s" not found in ancestor',[Name]) ;
     end else begin
        BaseEntry := GetFuncSignature(Entry,TFuncType(DataType),False);
        if (Directive = drOverride) then
        begin
           if not Entry.IsCode then
              raise ECompException.Createfmt('cannot override "%s"',[Name]);
           if (BaseEntry=nil)or not BaseEntry.IsVirtualFunc() then
              raise ECompException.Createfmt('cannot override "%s"',[Name]);
           if AMember.Visibility <>BaseEntry.Visibility   then
              Msg_Report(msWarning,LoadResString(@VISIBILITY_LEVEL_ERR),GetLine());
        end else begin
            if (BaseEntry<>nil)and BaseEntry.IsVirtualFunc and not (Directive in [drOverride,drNew]) then
                Msg_Report(msWarning,Format('hide virtual member "%s"',[Name]),GetLine());
        end;
      end;
   end;
end;

function TComp.FuncProcessHeader(AModifiers:TDclModifiers):TFuncHeaderInf;
var
  tp:TDataType;
  FunNew:TFuncType;
  funcEntry,OverLoadExpr:TSymIdent;
  Dsf:TFuncHeaderInf;
  Found:TSymIdent;
  StartingScope:TObject;
  BindIntrf :TIntrfImplementation;
begin
    FillChar(Result,Sizeof(Result),0);
    StartingScope := FStacks[ssFuncList];
    if CurrentToken = uuStatic then
    begin
       AModifiers:=AModifiers+[dmStatic];
       Nexttoken();
    end;
    tp :=TypeDecl([dmVoidDcl,dmPtrDcl,dmTypeRequired]);
    BindIntrf := InterfaceFuncSelector();
    if BindIntrf<> nil then
       CheckCurrentAndMove(uuOpDot);
    Dsf := AbsoluteFuncSelector(AModifiers);

    Result.Exists:= Dsf.Exists;
    Result._Name := Dsf._Name;
    funcEntry := Dsf.Header;
    if IsGlobalScope() and not(dmStatic in AModifiers) then
       Err(@STATIC_FUNC_EXPECTED);
    Result.Header :=ArgsListDcl(tp,AModifiers);
    FunNew:=TFuncType(Result.Header.DataType);
    if not Result.Exists then
    begin //add new function
       if StartingScope<>FStacks[ssFuncList] then
          Err(@FUNC_EXPECTED);
       funcEntry:= NewSymbol(Dsf._Name,ssNamesList,AModifiers,FunNew);
       funcEntry.ObjLocation :=olCode;
       FUnit.Allocate(funcEntry);
    end else begin
       if not funcEntry.IsCode or not funcEntry.DataType.IsFuncType then
          Err(@FUNC_NAME_EXPECTED);
       if funcEntry.FindSignature(FunNew,Found)then
       begin
          if not FunNew.IsEqual(Found.DataType) then
             Err(@INCOMPATIBLE_TYPE);
          if not FunNew.ParamsNamesEqual(Found.DataType) then
             Err(@PARAMS_NAMES_ERR);
          if (AModifiers*[dmPrivate..dmPublic,dmNew..dmAbstract])<> [] then
              Msg_Report(msError,LoadResString(@INVALID_MODIFIER),GetLine());
          funcEntry:=Found;
       end else begin
          if StartingScope<>FStacks[ssFuncList] then
             Err(@FUNC_EXPECTED);
          OverLoadExpr := TScope(FStacks[ssFuncList]).NewSymbol(TSymIdent);
          SetSymProps(OverLoadExpr,Dsf._Name,AModifiers,FunNew);
          OverLoadExpr.ObjLocation :=olCode;
          funcEntry.AddOverload(OverLoadExpr);
          Result.Exists :=False;
          funcEntry:=OverLoadExpr;
          FUnit.Allocate(funcEntry);
       end;
    end;
    if (dmStatic in AModifiers)and ((dmClassMthd in AModifiers)or funcEntry.IsVirtualFunc()) then
        Err(@INVALID_MODIFIER);
    if IsClassScope() then
    begin
       Check_Class_Symbol(funcEntry,BindIntrf,TClassStmt(FStacks[ssFuncList]));
    end;
    Result.Header :=funcEntry;
end;

function TComp.IsClassScope():boolean;
begin
  Result := (FStacks[ssFuncList] is TInheritedType)
               and (TInheritedType(FStacks[ssFuncList]).DataType.IsClass);
end;

function TComp.IsInterfaceScope():boolean;
begin
  Result := (FStacks[ssFuncList] is TInheritedType)
               and (TInheritedType(FStacks[ssFuncList]).DataType.IsInterface );
end;

function TComp.IsGlobalScope():boolean;
begin
  Result := FStacks[ssFuncList]=FUnit;
end;

procedure TComp.Func_Stmt(AModifiers:TDclModifiers);
const
  FUNC_MOSIFIERS :TDclModifiers=[dmPrivate..dmPublic,dmStatic,dmFuncForward];
  CLASS_MOSIFIERS:TDclModifiers=[dmClassMthd,dmNew,dmVirtual,dmOverride,dmAbstract];
var
  Ac:TFuncHeaderInf;
  IsForwardDcl:boolean;
  Level:integer;
begin
  //  if not(dmMaker in AModifiers) then
       CheckCurrentAndMove(uuFunc);

    if IsClassScope() then
       ModifiersCheck(AModifiers,FUNC_MOSIFIERS+CLASS_MOSIFIERS)
    else if IsInterfaceScope() then
       ModifiersCheck(AModifiers,[dmFuncForward,dmAbstract])
    else
       ModifiersCheck(AModifiers,FUNC_MOSIFIERS);
    Level :=FStacks.Level;
    if FActiveFunc <> nil then
       Err(@NESTED_FUNC_ERR);
    Ac :=FuncProcessHeader(AModifiers);
    IsForwardDcl :=NextToken() = uuInstSep;
    if not IsForwardDcl and (dmFuncForward in AModifiers) then
       Err(@FORWARD_NEEDED);
    if SameText(Ac.Header.Name,'main') then
       Ac.Header.Used:=True;
    if Ac.Exists then
    begin
       if IsForwardDcl or (Ac.Header.Value.vPtr<> nil) then
          Err(@REDECLARED_FUNC);
    end;
    if not IsForwardDcl then //Forward Dcl test
    begin // implementation
       if Ac.Header.Directive =drAbstract then
          Err(@ABSTRACT_BIND_ERROR);
       FStacks.Push(TObject(esLocal),[ssActiveErrSync]);
       FunctionBlock(Ac.Header);
       FStacks.Pop();
       while Level < FStacks.Level do
         FStacks.Pop(); //pused in AbsoluteFuncSelector
    end;
end;

function TComp.Block():TStmt;
var
  Nw:TAllocDeclStmt;
begin
   Nw:=NewScope(TAllocDeclStmt);
   Nw.DefaultVarClass := olAuto;
   EnterScope(Nw,[ssNamesList,ssConstsList]);
   CheckCurrentToken(uuBrassL);
   Result := StmtList();
   CheckCurrentToken(uuBrassR);
   ExitScope();
end;

function TComp.StmtList():TStmtList;
var
 S:TStmt;
begin
    Result := NewStmt(imListStmt,TStmtList);
    FStacks.Push(Result,[ssActiveCodeStmt]);
    NextToken();
    repeat
       S:=nil;
       try
          case CurrentToken of
              uuConst:Const_Stmt([dmPrivate]);
             uuStatic:Var_Stmt([dmPrivate,dmStatic]);
           uuReadonly:Var_Stmt([dmPrivate,dmStatic,dmReadonly]);
               uuType:Type_Stmt([dmPrivate,dmExtentedType,dmPtrDcl,dmArrayDcl]);
                uuVar: Var_Stmt([dmPrivate,dmAuto]); //local initializer
               uuNone:break;
          else
             S :=Stmt(False,False);
             if S = nil then
                 break;
          end;
          if S <> nil then
             Result.List.Add(S);
          NextToken();
       except on e:ECompException do
          begin
             Msg_Report(msError,e.Message);
             ErrorSync();
          end;
       end;
    until False;
    FStacks.Pop();
end;

procedure TComp.ExitScope();
begin
   FStacks.Pop();
end;

procedure TComp.EnterScope(AObj: TAllocDeclStmt; ALists: TListKindSet);
begin
  FStacks.Push(AObj,ALists+[ssAlloc]);
end;

function TComp.NewScope(AScopeClass:TAllocDeclStmtClass):Pointer;
var
 Scp:TSymIdent;
begin
  Scp   :=NameStacks[ssNamesList].NewSymbol(AScopeClass);
  Result:=TAllocDeclStmt(Scp);
end;

{**************************************************************************************
********************************   Expressions         ********************************
**************************************************************************************}

function TComp.NewActualArgsList():TExprList;
begin
    Result := TExprList.Create;
    FfreeList.Add(Result);
    ExpressionList(Result);
end;

function TComp.PrimaryBaseExpr():TExpr;
begin
    Result := nil;
    case CurrentToken of
            uuIdent:Result := IdentExpr();
        uuIntNumber:Result := LiteralConstExpr();
        uuHexNumber:Result := LiteralConstExpr();
      uuFloatnumber:Result := LiteralConstExpr();
        uuCharacter:Result := LiteralConstExpr();
             uuNull:Result := LiteralConstExpr();
             uuTrue:Result := LiteralConstExpr();
            uuFalse:Result := LiteralConstExpr();
             uuText:Result := LiteralConstExpr();
            uuExprL:Result := ParanthesizedExpr();
             uuBase:begin
                  Result := BaseExpr();
                  Exit;
             end;
    end;
    if Result = nil then
       Exit;
    NextToken();
   // Result.ExpectRValue();
end;

function TComp.PrimaryExpr():TExpr;
begin
    Result := PrimaryBaseExpr();
    if Result = nil then
       Exit;
    while CurrentToken=uuOpdot do
          Result:= MemberAccessExpr(Result);
   // Result.ExpectRValue();
    Result:= PostFixExpr(Result);
    Result.ExpectRValue();
    if CurrentToken = uuAs then
       Result := AsExpr(Result);
end;

function TComp.PostFixExpr(PrevExpr:TExpr):TExpr;
begin
    PrevExpr.ExpectRValue();
    Result :=PrevExpr;
    if Result <> nil then
    begin
      repeat
        case CurrentToken of
            uuExprL:Result:= InvocationExpr(Result);
            uuOpinc:Result:= PostIncExpr(Result);
            uuOpdec:Result:= PostDecExpr(Result);
             uuIdxL:Result:= ElementAccessExpr(Result);
            uuOpDot:Result:= MemberAccessExpr(Result);
        uuMemberPtr:Result:= MemberPtrExpr(Result);
        else
           Break;
        end;
      until False;
    end;
end;

function TComp.MakeRef(AExpr:TExpr;AType:TDataType):TExpr;
var
 Ref:TExpr;
begin
   if not AExpr.IsAddressable() then
      raise ECompException.CreateRes(@ADDRESS_EXPECTED);
   Ref := NewExpr();
   Ref.Assign(AExpr);
   Ref.SetDataType(MakePointerType(AType));
   Result := NewDerefExpr(Ref);
   Result.xOp := imRef;
   TOprExpr(Result).Expr2 := AExpr;
end;

function TComp.GetSelfExpr(AType:TDataType):TExpr;
begin
   if (FActiveFunc = nil) or not FActiveFunc.Header.IsMethod()then
      Err(@NO_ACTIVE_CLASS);
   Result := FActiveFunc.SelfExpr;
   if Result.QureyKind = atReference then
      Result := MakeRef(Result,AType);
end;

function TComp.BaseExpr():TExpr;
var
 Mbr:TSymIdent;
 AClass:TClassStmt;
begin
   AClass := TClassStmt(FActiveFunc.SelfExpr.DataType.SymbInfo);
   if AClass.Ancestor = nil then
      Err(@NO_ANSCESROR);
   Result := GetSelfExpr(AClass.Ancestor.DataType);
   if TryNextToken(uuExprL) then // inherited
   begin
       with FActiveFunc.Header do
       begin
          Mbr := FindOverloadFunc(Name,AClass.Ancestor,TFuncType(DataType),False);
          if Mbr = nil then
             raise ECompException.Createfmt(LoadResString(@ANCESTOR_MEMBER_ERR),[Name]);
          Result := NewMemberExpr(Result,Mbr);
       end
   end else begin //member
       Result:=MemberAccessExpr(Result);
   end;
   if Result.xOp = imInstance then // isMethod
      TSymIdent(TOprExpr(Result).Expr2).Directive :=drNone;//avoid virtual call
   Result := PostFixExpr(Result);
end;

function TComp.MakeAbsolutIndex(ASym:TSymIdent):TExpr;
begin
  if ASym.ObjLocation in [olStatic,olCode] then
  begin
     Result :=ASym.Clone();
     TSymIdent(Result).NextSym :=ASym.NextSym;
     Result.Address :=ASym.Address or(ASym.BaseUnit.Address shl 16)
  end else
        Result := ASym;
end;

function TComp.IdentExpr:TExpr;
var
  Sym:TSymIdent;
  fld:TFieldType;
  mSelf:TExpr;
begin
   CheckCurrentToken(uuIdent);
   GetID(GetTokenTxt,TExpr(Sym),False,True);
   if Sym.IsField() or Sym.IsMethod() then
   begin
       FSymSearch.Text := Sym.Name;
       fld := TFieldType(GetActiveObject());
       mSelf := GetSelfExpr(fld.DataType);
       if not fld.FindMember(FSymSearch,TScope(FStacks[ssNamesList])) then
          raise ECompException.Createfmt('member not accessible %s',[GetTokenTxt]);
       Result := NewMemberExpr(mSelf,Sym);
   end else if Sym.QureyKind = atReference then
   begin
       Result :=MakeRef(Sym,Sym.DataType);
   end else if Sym.IsType() and Sym.DataType.IsClass then
   begin
       Result := MakeAbsolutIndex(TClassStmt(Sym.DataType.SymbInfo).VTable);
       Result.SetDataType(MakeMetaClassType(TClassType(Sym.DataType)))
   end else
          Result := MakeAbsolutIndex(Sym);
end;

function TComp.ParanthesizedExpr:TExpr;
var
 Expr:TExpr;
begin
   CheckCurrentToken(uuExprL);
   Expr:=Expression(True,True);
   Result := Expr;
   CheckCurrentToken(uuExprR);
end;

function TComp.InvocationExpr(PrevExpr:TExpr):TExpr;
var
 List:TExprList;
begin
    List:= NewActualArgsList();
    Result := NewCallExpr(PrevExpr,List);
    CheckCurrentToken(uuExprR);
    NextToken;
end;

function TComp.MemberPtrExpr(PrevExpr:TExpr):TExpr;
var        //->
 Member:TExpr;
begin
    Member := NewDerefExpr(PrevExpr);
    Result := MemberAccessExpr(Member);
end;

function TComp.ParseChar:Char;
var
 Txt:string;
 Ret:integer;
begin
   Txt := GetTokenTxt();
   Txt := Copy(Txt,2,Length(Txt)-2);// skip quotes
   Ret := -1;
   case Length(Txt)of
      1: Ret := Ord(Txt[1]);
      2:begin
         if Txt[1]='\' then
            case Txt[2] of
               '0': Ret := 0;
               'r': Ret := 13;
               'n': Ret := 10;
               't': Ret := 9;
               '\': Ret := Ord('\');
            end;
      end;
   end;
   if Ret = -1 then
      Err(@INVALID_CHAR);
   Result := Chr(Ret);
end;

function TComp.LiteralConstExpr:TExpr;
var
 Txt:string;
begin
   case CurrentToken of
      uuIntNumber: Result:=NewLiteralExpr(StrToInt(GetTokenTxt));
      uuHexNumber: Result:=NewLiteralExpr(StrToInt(GetTokenTxt));
    uuFloatnumber: Result:=NewLiteralExpr(StrToFloat(GetTokenTxt));
      uuCharacter: Result:=NewLiteralExpr(ParseChar());
           uuTrue: Result:=NewLiteralExpr(True);
          uuFalse: Result:=NewLiteralExpr(False);
           uuNull: Result:=NewLiteralExpr(nil);
           uuText:begin
                   Txt := GetTokenTxt();
                   Txt := Copy(Txt,2,Length(Txt)-2);
                   Result := NewLiteralExpr(Txt);
              end;
       else
          Result := nil;
    end;
end;

function TComp.NewResBucket():TResBucket;
begin
    Result := TResBucket.Create;
    Ffreelist.Add(Result);
end;

function TComp.SizeOfExpr():TExpr;
var
 dt:TDataType;
begin
   GetNextTokenAndCheck(uuExprL);
   NextToken();
   dt := TypeDecl([dmPtrDcl,dmArrayDcl]);
   if dt = nil then
   begin
     dt := IdentExpr().DataType;
     NextToken();
   end;
   Result := NewLiteralExpr(dt.TypeSize);
   CheckCurrentToken(uuExprR);
   NextToken();
end;

function TComp.PostDecExpr(PrevExpr:TExpr):TExpr;
begin
   Result := NewPostIncrExpr(imPostDec,PrevExpr);
   NextToken();
end;

function TComp.PostIncExpr(PrevExpr:TExpr):TExpr;
begin
   Result := NewPostIncrExpr(imPostInc,PrevExpr);
   NextToken();
end;

function TComp.ElementAccessExpr(PrevExpr:TExpr): TExpr;
begin
    if not PrevExpr.DataType.IsArray then
       raise ECompException.CreateRes(@ARRAY_EXPECTED);
    CheckCurrentToken(uuIdxL);
    Result := NewElementAccessExpr(PrevExpr,Expression(True,True));
    CheckCurrentAndMove(uuIdxR);
end;

function TComp.MemberAccessExpr(PrevExpr:TExpr): TExpr;
var
  Sym:TSymIdent;
  Scope:TScope;
begin
   NextToken();
   Scope := nil;
   if PrevExpr.DataType.IsMetaClass()then
      Scope := TScope(PrevExpr.DataType.Dest.SymbInfo)
   else if PrevExpr.DataType.SymbInfo is TScope then
      Scope := TScope(PrevExpr.DataType.SymbInfo);
   if (Scope = nil)or(Scope is TFuncHeaderStmt)then
      Err(@SCOPE_EXPECTED);
   CheckCurrentToken(uuIdent);
   FSymSearch.Text :=GetTokenTxt;
   if not Scope.FindMember(FSymSearch,NameStacks[ssNamesList]) then
      raise ECompException.Createfmt('member not found "%s"',[FSymSearch.Text]);
   Sym := FSymSearch.Mutch;
   if PrevExpr.IsRValue then
      Result := NewMemberExpr(PrevExpr,Sym)
   else
      Result := MakeAbsolutIndex(Sym);
   NextToken();
end;

function TComp.CastExpr:TExpr;
var
 dt:TDataType;
begin
    Result := nil;
    if CurrentToken <> uuExprL then
       Exit;
    Push();
    NextToken;
    dt :=TypeDecl([dmPtrDcl,dmArrayDcl]);
    if dt <> nil then
    begin
        if CurrentToken = uuExprR then
           Result :=NewCastExpr(GetUnary(),dt);
    end;
    Pop(Result<>nil);
end;

function TComp.UnaryExpr(AMove, Required:boolean):TExpr;
begin
    if AMove then
       NextToken();
    Result := CastExpr();
    if Result = nil then
       Result :=  PrimaryExpr();
    if Result = nil then
      case CurrentToken of
        uuOpMinus:Result := NewBinBaseExpr(imMinus,GetUnary(),nil);
         uuOpComp:Result := NewBinBaseExpr(imComp,GetUnary(),nil);
          uuOpNot:Result := NewBooleanExpr(imNot,GetUnary(),nil);
         uuOpPlus:Result := NewPlusExpr(GetUnary());
         uuOpStar:Result := NewDerefExpr(GetUnary());
          uuOpAnd:Result := NewAddrExpr(GetUnary());
          uuOpInc:Result := NewPreIncrExpr(imPreInc,GetUnary(),NewLiteralExpr(1));
          uuOpDec:Result := NewPreIncrExpr(imPreDec,GetUnary(),NewLiteralExpr(1));
         uuSizeOf:Result := SizeOfExpr();
            uuNew:Result := NewConstructor();
      end;
    if Result = nil then
    begin
       if Required then
          Err(@Expr_Expected);
    end;
end;

function TComp.GetUnary(): TExpr;
begin
   Result:=UnaryExpr(True,True);
end;

function TComp.MultiplicativeExpr(AExpr:TExpr): TExpr;
begin
   Result:=AExpr;
   if Result <> nil then
    while True do
    case CurrentToken of
       uuOpStar:Result := NewBinBaseExpr(imMul,Result,GetUnary());
        uuOpdiv:Result := NewBinBaseExpr(imDiv,Result,GetUnary());
      uuOpmodul:Result := NewBinBaseExpr(imModul,Result,GetUnary());
    else
       break;
    end;
end;

function TComp.AdditiveExpr(AExpr:TExpr): TExpr;
begin
   Result:=MultiplicativeExpr(AExpr);
   if Result <> nil then
    while True do
    case CurrentToken of
       uuOpMinus: Result:= NewBinBaseExpr(imSub,Result,MultiplicativeExpr(GetUnary()));
        uuOpPlus: Result:= NewBinBaseExpr(imAdd,Result,MultiplicativeExpr(GetUnary()));
    else
       break;
    end;
end;

function TComp.ShiftExpr(AExpr:TExpr): TExpr;
begin
   Result:=AdditiveExpr(AExpr);
   if Result <> nil then
    while True do
    case CurrentToken of
       uuOpShr: Result:= NewBinBaseExpr(imShr,Result,AdditiveExpr(GetUnary()));
       uuOpShl: Result:= NewBinBaseExpr(imShl,Result,AdditiveExpr(GetUnary()));
    else
       break;
    end;
end;

function TComp.RelationalExpr(AExpr:TExpr): TExpr;
begin
   Result:=ShiftExpr(AExpr);
   if Result <> nil then
    case CurrentToken of    // no associative
        uuOpless: Result:= NewBinBaseExpr(imLess,Result,ShiftExpr(GetUnary()));
          uuOpgr: Result:= NewBinBaseExpr(imGr,Result,ShiftExpr(GetUnary()));
       uuOpgrequ: Result:= NewBinBaseExpr(imGrEqu,Result,ShiftExpr(GetUnary()));
     uuOplessequ: Result:= NewBinBaseExpr(imLessEqu,Result,ShiftExpr(GetUnary()));
            uuIs: Result:= IsExpr(Result);
    end;
end;

function TComp.EqualityExpr(AExpr:TExpr): TExpr;
begin
   Result:=RelationalExpr(AExpr);
   if Result <> nil then
    case CurrentToken of    // no associative
        uuOpequ: Result:= NewBinBaseExpr(imEqu,Result,RelationalExpr(GetUnary()));
     uuOpnotequ: Result:= NewBinBaseExpr(imNotEqu,Result,RelationalExpr(GetUnary()));
    end;
end;

function TComp.LogicExpr(AExpr:TExpr): TExpr;
begin
   Result:=EqualityExpr(AExpr);
   if Result <> nil then
    while True do
    case CurrentToken of
      uuOpand: Result:= NewBinBaseExpr(imAnd,Result,EqualityExpr(GetUnary()));
       uuOpOr: Result:= NewBinBaseExpr(imOr,Result,EqualityExpr(GetUnary()));
      uuOpXor: Result:= NewBinBaseExpr(imXor,Result,EqualityExpr(GetUnary()));
    else
       break;
    end;
end;

function TComp.BoolExpr(AExpr:TExpr): TExpr;
begin
   Result:=LogicExpr(AExpr);
   if Result <> nil then
    while True do
    case CurrentToken of
       uuOpcmpand: Result:= NewBooleanExpr(imAndCmp,Result,LogicExpr(GetUnary()));
        uuOpcmpor: Result:= NewBooleanExpr(imOrCmp,Result,LogicExpr(GetUnary()));
    else
       break;
    end;
end;

function TComp.TestExpr(AExpr:TExpr): TExpr;
var
 B:TExpr;
begin
   Result:=BoolExpr(AExpr);
   if (Result <> nil)then// and(Result.Paranthesized)
   begin
      while CurrentToken = uuOpTest do
      begin
         B:=TestExpr(GetUnary());
         CheckCurrentToken(uuDef);
         Result:=NewTestExpr(Result,B,TestExpr(GetUnary()));
      end;
   end;
end;

function TComp.AssignExpr(AExpr:TExpr): TExpr;
begin
    case CurrentToken of
         uuopAssign: Result:=NewAssignExpr(AExpr,Expression(True,True));
       uuPlusAssign: Result:=NewPreIncrExpr(imPreInc,AExpr,Expression(True,True)); //+=
      uuMinusAssign: Result:=NewPreIncrExpr(imPreDec,AExpr,Expression(True,True)); //-=
    else
       Result:=  TestExpr(AExpr);
    end;
end;

function TComp.Expression(AMove, Required: boolean):TExpr;
begin
   Result := UnaryExpr(AMove,Required);
   if Result <> nil then
   begin
      Result:= AssignExpr(Result);
   end;
end;

function TComp.ConditionExpr():TExpr;
var
 LPos:integer;
begin
    GetNextTokenAndCheck(uuExprL);
    NextToken();
    LPos:=FPos;
    Result := Expression(False,True);
    LPos:=FPos-LPos;
    Result.ExpectConditionExpr();
    if Result.IsConstant and (not Result.Value.vBool or (LPos >1)) then
       Warning_Bool_Eval(Result.Value.vBool);
    CheckCurrentToken(uuExprR);
end;

function TComp.ExpectConstantExpr():TExpr;
begin
   Result := Expression(False,True);
   if not Result.IsConstant() then
      Msg_Report(msError,@CONSTANT_EXPR_EXPECED);
end;

function TComp.ExpressionList(ADest:TExprList):integer;
var
 Expr:TExpr;
begin
    Result := 0;
    Expr:= Expression(True,False);
    if Expr <> nil then
      repeat
         ADest.AddExpr(Expr);
         inc(Result);
         if CurrentToken <> uuSep then
            break;
         Expr := Expression(True,True);
      until Expr = nil;
end;

{***************************************************************************************
********************************      Statements        ********************************
***************************************************************************************}

function TComp.IsLabelStmt():boolean;
begin
   Result :=CurrentToken =uuIdent;
   if Result  then
   begin
      Push;
      Result :=NextToken =uuDef;
      Pop(False);
   end
end;

function TComp.Stmt(AMove,ARequired:boolean):TStmt;
begin
    if AMove then
       NextToken();
    case CurrentToken of
             uuIf: Result:= If_Stmt();
          uuWhile: Result:= While_Stmt();
          uuBreak: Result:= Break_Stmt();
       uuContinue: Result:= Continue_Stmt();
             uuDo: Result:= Do_Stmt();
         uuBrassL: Result:= Block();
         uuSwitch: Result:= Switch_Stmt();
            uuFor: Result:= For_Stmt();
           uuGoTo: Result:= GoTo_Stmt();
         uuReturn: Result:= Return_Stmt();
            uuTry: Result:= Try_Stmt();
          uuThrow: Result:= Throw_Stmt();
          uuPrint: Result:= Print_Stmt();
        uuInstSep: Result:= NewStmt(imEmptyStmt,TStmt);
        else if IsLabelStmt() then  // label stmt
           Result := Label_Stmt()
        else begin
           Result := Expr_Stmt();
           if Result <> nil then
              CheckCurrentToken(uuInstSep);
        end;
      end;
      if (Result=nil)and ARequired then
         Err(@INSTRUCTION_EXPECTED);
end;

function TComp.NewConstructor():TOprExpr;
var
 Cls:TClassStmt;
 ObjInstance,C,Tmp:TExpr;
 ConstructorFunc:TSymIdent;
begin
  NextToken();
  C := PrimaryBaseExpr();
  if (C=nil)or not c.DataType.IsMetaClass then
     Err(@CLASS_TYPE_EXPECTD);
  Cls := TClassStmt(C.DataType.Dest.SymbInfo);
  FSymSearch.Text:='Loader';//
  if not Cls.FindMember(FSymSearch,Cls)then
     raise ECompException.Create('cant not find constructor');
  ConstructorFunc := FSymSearch.Mutch;
  Tmp:=AllocatTemp(Cls.DataType);
  Result := NewExpr(imConstructor,nil,nil);
  Result.Assign(Tmp); // copy index of the temp var
  Result.Expr1 := C;
  ObjInstance  := NewMemberExpr(Tmp,ConstructorFunc);
  Result.Expr2 := InvocationExpr(ObjInstance);

  if not ConstructorFunc.DataType.Dest.IsVoidType()then
     Err(@CONSTRUCTOR_TYPE_ERR);
end;

function TComp.Simple_StmtList():TStmtList;
var
 S:TStmt;
begin
  Result := NewStmt(imListStmt,TStmtList);
  S := Expr_Stmt();
  if S = nil then
     Exit;
  Result.List.Add(S);
  while CurrentToken = uuSep do
  try
      NextToken();
      S := Expr_Stmt();
      if S=nil then
         Err(@INSTRUCTION_EXPECTED);
      Result.List.Add(S);
  except on e:ECompException do
       Msg_Report(msError,e.Message);
  end;
end;

function TComp.Expr_Stmt():TStmt;
const VALID_EXPRS:set of TQsCmdInst=
            [imAssign,imPreInc,imPreDec,
             imPostInc,imPostDec,imInvocation];
var
 vExpr:TExpr;
 S:TExprStmt;
begin
    vExpr := Expression(False,False);
    Result := nil;
    if vExpr <> nil then
    begin
      if not(vExpr.xOp in VALID_EXPRS)then
         Err(@INVALID_INSTRUCTION);
      S := NewStmt(imExprStmt,TExprStmt);
      S.Expr :=vExpr;
      Result := S;
    end
end;

function TComp.GetLabel():TLabelStmt;
var
 Lab:TSymIdent;
begin
   CheckCurrentToken(uuIdent);
   FSymSearch.Text :=GetTokenTxt();
   if ActiveFunc.FindMember(FSymSearch,NameStacks[ssNamesList]) then
   begin
       Lab :=FSymSearch.Mutch;
       if Lab.ObjLocation <> olLabel then
          Err(@LABEL_EXPECTED);
       Result:= Lab.Value.vPtr;
       if Result.Section <> FActiveSection then
          Err(@TRY_SECTION_ERROR);
   end else begin
       Lab:=ActiveFunc.NewSymbol(GetTokenTxt(),TSymIdent);
       Lab.SetDataType(VoidType.DataType);
       Lab.ObjLocation:=olLabel;
       Result := NewStmt(imLabelStmt,TLabelStmt);
       Lab.Value.vPtr :=Result;
       Result.Section  := FActiveSection;
   end;
end;

function TComp.Label_Stmt():TStmt;
var
 St:TLabelStmt;
begin
   St  :=GetLabel();
   if St.Stmt<>nil then
      Err(@LABEL_EXISTS);
   GetNextTokenAndCheck(uuDef);
   St.Stmt :=Stmt(True,True);
   Result:=St;
end;

function TComp.GoTo_Stmt():TStmt;
var
 Gt:TSimpleStmt;
begin
   Gt:=NewStmt(imGoToStmt,TSimpleStmt);
   NextToken();
   Gt.S:=GetLabel();
   GetNextTokenAndCheck(uuInstSep);
   Result:=Gt;
end;

function TComp.If_Stmt():TStmt;
var
 s1,s2:TStmt;
 C:TExpr;
 Ifstmt:TIfStmt;
begin
   Ifstmt := NewStmt(imIfStmt,TIfStmt);
   C:=ConditionExpr();
   s1 := Stmt(True,True);
   s2:= nil;
   if TryNextToken(uuElse) then
       s2:= Stmt(True,True);
   Ifstmt.Cond := C;
   Ifstmt.TrueStmt  :=s1;
   Ifstmt.FalseStmt :=s2;
   Result := Ifstmt;
end;

function TComp.While_Stmt():TStmt;
var
 WhileStmt:TWhileStmt;
begin
  WhileStmt:=NewStmt(imWhileStmt,TWhileStmt);
  WhileStmt.StmtsJumps :=FStmtsJumps;
  FStmtsJumps := WhileStmt;
  WhileStmt.Cond:=ConditionExpr();
  WhileStmt.Stmt :=Stmt(True,True);
  FStmtsJumps := WhileStmt.StmtsJumps;
  Result := WhileStmt;
end;

function TComp.Do_Stmt():TStmt;
var
 DoStmt:TDoStmt;
begin
  DoStmt:=NewStmt(imDoStmt,TDoStmt);
  DoStmt.StmtsJumps:=FStmtsJumps;
  FStmtsJumps := DoStmt;
  DoStmt.Stmt :=Stmt(True,True);
  GetNextTokenAndCheck(uuWhile);
  DoStmt.Cond:=ConditionExpr();
  GetNextTokenAndCheck(uuInstSep);
  FStmtsJumps := DoStmt.StmtsJumps;
  Result := DoStmt;
end;

function TComp.For_Stmt():TStmt;
var
 OldJmps:TLoopStmt;
 ForStmt:TForStmt;
 Nw:TAllocDeclStmt;
begin
    ForStmt := NewStmt(imForStmt,TForStmt);
    OldJmps:=FStmtsJumps;
    FStmtsJumps := ForStmt;
    GetNextTokenAndCheck(uuExprL);
    NextToken();
    Nw:=NewScope(TAllocDeclStmt);
    Nw.DefaultVarClass := olAuto;
    EnterScope(Nw,[ssNamesList]);
    if TryCurrentToken(uuVar) then
    begin
      Var_Dcl([dmInitializer,dmAuto,dmPrivate]);
    end;
    ForStmt.InitExpr:=Expr_Stmt();
    CheckCurrentAndMove(uuInstSep);
    ForStmt.CondExpr:= Expression(False,False);
    if ForStmt.CondExpr<> nil then
    begin
      ForStmt.CondExpr.ExpectConditionExpr();
      if ForStmt.CondExpr.IsConstant() then
         Warning_Bool_Eval(ForStmt.CondExpr.Value.vBool);
    end;
    CheckCurrentAndMove(uuInstSep);
    ForStmt.ExprsOpt:= Simple_StmtList();
    CheckCurrentToken(uuExprR);
    ForStmt.S := Stmt(True,True);
    FStmtsJumps := OldJmps;
    Result := ForStmt;
    ExitScope();
end;

function TComp.GetCurrentStmtsJumps():TLoopStmt;
begin
   Result :=FStmtsJumps;
   repeat
      if not(Result is TTryHandler) then
         break;
      Result := TTryHandler(Result).ParentLoopStmt;
   until False;
   if Result = nil then
      Err(@LOOP_EXPECTED);
end;

function TComp.Break_Stmt():TStmt;
begin
   GetNextTokenAndCheck(uuInstSep);
   GetCurrentStmtsJumps();
   Result:=NewStmt(imBreakStmt,TStmt);
   Result.StmtsJumps:=FStmtsJumps;
end;

function TComp.Continue_Stmt():TStmt;
begin
   GetNextTokenAndCheck(uuInstSep);
   if GetCurrentStmtsJumps().xOp = imSwitchStmt then
      Err(@LOOP_EXPECTED);
   Result:=NewStmt(imContinueStmt,TStmt);
   Result.StmtsJumps:=FStmtsJumps;
end;

function TComp.Try_HandlerSection():TSimpleStmt;
var
 OldSection:TSimpleStmt;
begin
   Result :=NewStmt(imNone,TSimpleStmt);
   FStacks.Push(Result,[ssFinallySection]);
   OldSection := FActiveSection;
   FActiveSection:= Result;
   Result.S:=Block();
   FActiveSection:= OldSection;
   FStacks.Pop();
end;

function TComp.Try_Stmt():TStmt;
var
 TryHandler:TTryHandler;
 OldSection:TSimpleStmt;
 SList:TStmtList;
 CatchStmt:TCaseStmt;
 Value:integer;
begin
   TryHandler :=NewStmt(imNone,TTryHandler);
   TryHandler.Exec :=NewStmt(imNone,TSimpleStmt);
   TryHandler.ParentTryHandler :=FActiveTryHandler;
   FActiveTryHandler :=TryHandler;
   TryHandler.ParentLoopStmt :=FStmtsJumps;
   FStmtsJumps :=TryHandler;
   TryHandler.CodeStmt := ActiveFunc;
   OldSection:=FActiveSection;
   FActiveSection:= TryHandler.Exec;
   NextToken();
   TryHandler.Exec.S:=Block();
   FActiveSection := OldSection;
   FStmtsJumps := nil;//no jump in Finally/Catch section
   case NextToken of
      uuFinally:begin
         TryHandler.xOp := imFinallyStmt;
         NextToken();
         TryHandler.Handler :=Try_HandlerSection();
       end;
      uuCatch:begin
         TryHandler.xOp := imCatchStmt;
         TryHandler.Handler := NewStmt(imNone,TSimpleStmt);
         SList :=NewStmt(imListStmt,TStmtList);
         TryHandler.Handler.S :=SList;
         repeat
            Value:=-1;
            NextToken();
            CatchStmt:=NewStmt(imNone,TCaseStmt);
            if CurrentToken = uuIntNumber then
            begin
                Value := StrToInt(GetTokenTxt());
                NextToken();
                CheckCurrentAndMove(uuDef)
            end;
            CatchStmt.S := Try_HandlerSection();
            CatchStmt.Value := NewLiteralExpr(Value);
            if Value=-1 then
            begin
              TryHandler.DefaultErrHandler:=CatchStmt;
              break;
            end;
            SList.List.Add(CatchStmt);
         until not TryNextToken(uuCatch);
      end;
   else
      Err(@TRY_HANDLER_EXPECTED);
   end;
   TryHandler._EndHandler :=NewStmt(imNone,TStmt);// line number
   FStmtsJumps :=TryHandler.ParentLoopStmt;
   FActiveTryHandler :=TryHandler.ParentTryHandler;
   Result :=TryHandler;
end;

function TComp.Throw_Stmt():TStmt;
var
 ThrowStmt:TExprStmt;
begin
   NextToken();
   ThrowStmt:=NewStmt(imThrowStmt,TExprStmt);
   ThrowStmt.Expr := PrimaryExpr();
   if ThrowStmt.Expr = nil then
   begin   // TTryHandler(FStacks[ssFinallySection])
      if (FActiveTryHandler= nil) or (FStacks[ssFinallySection]=nil)
         or(FActiveTryHandler.xOp <> imCatchStmt) then
         Msg_Report(msError,@EXCEPT_SECTION_EXPEC);
   end else
      if not ThrowStmt.Expr.DataType.IsOrdinalType then
         raise ECompException.CreateRes(@ORDINAL_TYPE_EXPECTED);
   CheckCurrentToken(uuInstSep);
   Result :=ThrowStmt;
end;

function TComp.Return_Stmt():TStmt;
var
 Rt:TReturnStmt;
 RetType:TDataType;
 Expr,Ret:TExpr;
begin
   if FStacks[ssFinallySection]<> nil then
      Msg_Report(msError,@NO_JUMP_HANDLER);
   NextToken();
   Rt:=NewStmt(imReturnStmt,TReturnStmt);
   Rt.CodeStmt :=ActiveFunc ;

   Expr:=Expression(False,False);
   RetType := Rt.CodeStmt.Header.DataType.Dest;
   if Expr = nil then
      Expr:=VoidType;
   if not Expr.DataType.IsVoidType() then
   begin
      Expr := NewImplicitConv(Expr,RetType);  // option
      Ret := GetActiveFuncBlock().ReturnExpr;
      Ret := MakeRef(Ret,Ret.DataType);
      Rt.xExprs :=NewExpr(imNone,Ret,Expr);
   end;
   Rt.Handler:=FActiveTryHandler;
   CheckCurrentToken(uuInstSep);
   Result:=Rt;
end;

function TComp.Switch_Stmt():TStmt;
var
 expr,testExpr:TExpr;
 Sw:TSwitchStmt;
 Cs:TCaseStmt;
 I:integer;
begin
    Sw:=NewStmt(imSwitchStmt,TSwitchStmt);
    Sw.StmtsJumps:=FStmtsJumps;
    FStmtsJumps := Sw;
    NextToken;
    testExpr:=ParanthesizedExpr(); //  test expr type
    if not testExpr.DataType.IsOrdinalType then
       Msg_Report(msError,@ORDINAL_TYPE_EXPECTED);
    GetNextTokenAndCheck(uuBrassL);
    NextToken;
    if not testExpr.IsConstant() then
    begin
       expr:=NewExpr(imNone,testExpr,nil);
       expr.SetDataType(testExpr.DataType);
       expr.ObjLocation :=olTemp;
       testExpr :=expr;
    end;
    Sw.xExpr :=testExpr;
    while (CurrentToken = uuCase)or (CurrentToken =uuDefault)do
      try
         Cs:=NewStmt(imNone,TCaseStmt);
         if CurrentToken = uuCase then
         begin
            NextToken;
            Cs.Value:= ExpectConstantExpr();
            Cs.xExpr:= NewImplicitConv(Cs.Value,testExpr.DataType);
            for I := 0 to Sw.CasesList.List.Count-1 do
             with Sw.GetCase(I) do
              if (Value <> nil) and(Value.Value.vInt = Cs.Value.Value.vInt) then
                raise ECompException.Create('duplicated case in switch');
         end else begin
            if Sw.DefaultStmt<> nil then
               raise ECompException.Create('duplicated default in switch');
            Sw.DefaultStmt := Cs;
            NextToken;
         end;
         Sw.CasesList.List.Add(Cs);
         CheckCurrentToken(uuDef);
         Cs.S :=StmtList();
      except on e:ECompException do
        begin
           Msg_Report(msError,e.Message);
           while not (CurrentToken in [uuNone,uuCase,uuDefault])do
              NextToken();
        end;
      end;
    CheckCurrentToken(uuBrassR);
    FStmtsJumps := Sw.StmtsJumps;
    Result := Sw;
end;

function TComp.Print_Stmt():TStmt;
var
 Prn:TPrintStmt;
 Expr:TExpr;
begin
   NextToken();
   Prn:=NewStmt(imPrintStmt,TPrintStmt);
   Expr :=Expression(False,True);
   Prn.ByRef := Expr.DataType.IsCharArray();
   if Expr.DataType.IsCharArray then // by ref
      Prn.Expr := InternalAddr(Expr)
   else
      Prn.Expr := Expr;
   with Expr.DataType do
    if not(TypeClass in [tcInteger,tcChar,tcPointer,tcBool,tcFloat,tcEnum])
       and not IsCharArray then
          raise ECompException.Create('invalid type print');
   CheckCurrentToken(uuInstSep);
   Result := Prn;
end;

function TComp.NewInitializer(AType: TDataType;AStatic:boolean):TExpr;
var
   List:TInitializerExpr;
   function Load_Element(dst: TDataType):TExpr;
   begin
     Result := Expression(False,True);
     if AStatic then
      if not Result.IsConstant()and not IsPtrLink(Result) then
         Msg_Report(msError,@CONSTANT_EXPR_EXPECED);
     if Result.DataType.IsCharArray()and dst.IsCharArray() then   // string
     begin
        if dst.IsOpenArray then
           TArrayType(dst).Count := TArrayType(Result.DataType).Count
        else if TArrayType(dst).Count< TArrayType(Result.DataType).Count then
           Err(@INITIALIZER_ERROR);
     end;
     Result := NewImplicitConv(Result,dst);
   end;
   function Load_Elemts(dt: TDataType):integer;
   begin
      CheckCurrentToken(uuBrassL);
      if not dt.IsArray  then
         Err(@INITIALIZER_ERROR);
      Result:= 0;
      if TryNextToken(uuBrassR) then
      begin
        NextToken();
        Exit;
      end;
      repeat
           if NextToken() = uuBrassL then
              Load_Elemts(dt.Dest)
           else
              List.Elements.AddExpr( Load_Element(dt.Dest));
           Inc(Result);
      until CurrentToken<>uuSep;
      if not dt.IsOpenArray then
         if Result<>TArrayType(dt).Count then
            Err(@INITIALIZER_ERROR);
      TArrayType(dt).Count := Result;// force update size of array
      CheckCurrentAndMove(uuBrassR);
   end;
begin
   if CurrentToken = uuBrassL then
   begin
      List:=NewInitializerListExpr();
      Load_Elemts(AType);
      Result := List;
   end else begin
      Result := Load_Element(AType);
   end;
end;

function TComp.NewLocalInitializer(ADest: TExpr): TStmt;
var
  init: TInitStmt;
begin
  init :=NewStmt(imExprInitStmt,TInitStmt);
  init.Src := NewInitializer(ADest.DataType,False);
  init.Dst := ADest;
  Result := init;
end;

function TComp.GetNameStacks(AIdx: TListKind): TAllocDeclStmt;
begin
   Result :=TAllocDeclStmt(FStacks[AIdx]);
end;

function TComp.GetActiveCodeStmt: TStmtList;
begin
   Result :=TStmtList(FStacks[ssActiveCodeStmt]);
end;

function TComp.GetActiveErrSync: TErrSync;
begin
   Result :=TErrSync(FStacks[ssActiveErrSync]);
end;

function TComp.GetActiveFuncBlock: TFuncBlockStmt;
begin
    if FActiveFunc = nil then
       Err(@NO_ACTIVE_FUNC);
    Result :=FActiveFunc;
end;

function TComp.GetActiveObject: TAllocDeclStmt;
begin
    Result :=TAllocDeclStmt(FStacks[ssObjectList]);
    if Result = nil then
       Err(@NO_ACTIVE_CLASS);
end;

function TComp.GetSymByTag(AIdx: integer): TSymIdent;
begin
   Result :=TSymIdent(TTypeMembers(FUnit.DataType).Members.GetExpr(AIdx and $FFFF));
end;

function TComp.TxtToStaticStorage(ATxtExpr: TExpr): TExpr;
var
  C:TSymIdent;
begin
  C:= FUnit.NewSymbol(TSymIdent);
  C.Used := True;
  C.SetDataType(ATxtExpr.DataType);
  C.Value.vPtr := ATxtExpr ;
  AllocateStatic(C);
  Result:=MakeAbsolutIndex(C);
end;

function TComp.InternalAddr(AExpr: TExpr): TExpr;
begin
   if AExpr.IsConstant and AExpr.DataType.IsCharArray then
      AExpr:=TxtToStaticStorage(AExpr);
   Result := NewAddrExpr(AExpr);
end;

function TComp.IsPtrLink(AExpr: TExpr): boolean;
var
 Expr:TExpr;
begin
  Expr :=TOprExpr(AExpr).Expr1;
  Result:=(AExpr.xOp=imAddr)and((Expr.ObjLocation = olCode)
           or(Expr.ObjLocation = olStatic));
  if Result and(Expr.xOp=imOffset)then
  begin
     Result := TOprExpr(Expr).Expr2.IsConstant();
  end;
end;

function TComp.GetModifiers():TDclModifiers;
   procedure AddModifier(AModif:TDclModifier);
   begin
       Result := Result+[AModif];
       NextToken;
   end;
var
 md:TDclModifier;
begin
   Result :=[];
   NextToken;
   md := dmNone;
   case CurrentToken of
        uuPublic :md := dmPublic;
        uuPrivate:md := dmPrivate;
      uuProtected:md := dmProtected;
        uuLocal  :begin
           md := dmLocal;
           if TryNextToken(uuProtected)then
              md := dmLocalProtected;
        end;
    end;
    if md <> dmNone then
       AddModifier(md);
   // if CurrentToken = uuReadonly then
   //    AddModifier(dmReadonly);
    md := dmNone;
    case CurrentToken of
          uuNew   : md := dmNew;
         uuVirtual: md := dmVirtual;
        uuOverride: md := dmOverride;
        uuAbstract: md := dmAbstract;
    end;
    if md <> dmNone then
       AddModifier(md);
    if CurrentToken = uuStatic then
       AddModifier(dmStatic);
    if CurrentToken = uuClass then
       AddModifier(dmClassMthd);
end;

function TComp.NewInitializerListExpr: TInitializerExpr;
begin
    Result:=TInitializerExpr.Create;
    Result.xOp :=imInitList;
    ffreelist.Add(Result);
end;



function TComp.UnitChanged: boolean;
begin
   Result := TSynEdit(Data).TextVersion <> self.TxtVersion
end;

{ TUnitComp }

procedure TUnitComp.ProcessHeaderSection;
var
 Txt:string;
 oStream:TMemoryStream;
begin
  UsesStmt();
  FStacks.Push(TObject(esHeader),[ssActiveErrSync]);
  NextToken();
  repeat
     try
        case CurrentToken of
             uuFunc:Func_Stmt([dmFuncForward]);
            uuConst:Const_Stmt([dmPublic]);
           uuStatic:Var_Stmt([dmPublic,dmStatic]);
         uuReadonly:Var_Stmt([dmPublic,dmStatic,dmReadonly]);
             uuType:Type_Stmt([dmPublic,dmExtentedType,dmPtrDcl,dmArrayDcl]);
             uuNone,uuLink:break;
             uuImplementation:break;
        else
            raise ECompException.Create('error '+TokenName(CurrentToken));
        end;
        NextToken();
     except on e:ECompException do
        begin
           Msg_Report(msError,e.Message);
           ErrorSync();
        end;
     end;
  until False;
  FStacks.Pop();
  FImplPos := -1;
  if State = ssCompiled then
     Exit;
  //CheckCurrentToken(uuImplementation);
  if CurrentToken = uuImplementation then
  begin
    State  :=ssSourceSec;
    TUnit(FUnit).ToggleToImplementation();
    FImplPos := FPos;
    if TryNextToken(uuLink) then
    begin
       NextToken();
       Txt := GetTokenTxt();
       Txt := Copy(Txt,2,Length(Txt)-2);
       oStream:=TMemoryStream.Create;
       oStream.Size := Length(Txt) div 2;
       HexToBin(PChar(Txt),PChar(oStream.Memory),Length(Txt));
       FGenerator.BinObj.LoadFromStream(oStream);
       FGenereted := True;
    end else begin
      ProcessSourceSection();
    end;
  end;
end;

procedure TUnitComp.CreateUnit;
begin
  FUnit :=TUnit.Create;
  FUnit.Name := Name;
end;

procedure TUnitComp.ProcessSourceSection;
begin
    UsesStmt();
    FStacks.Push(TObject(esSource),[ssActiveErrSync]);
    FUnit.DefaultVisibility := vsPrivate;
    NextToken();
    repeat
       try
          case CurrentToken of
               uuFunc:Func_Stmt([]);
              uuConst:Const_Stmt([dmPrivate]);
             uuStatic:Var_Stmt([dmPrivate,dmStatic]);
           uuReadonly:Var_Stmt([dmPrivate,dmStatic,dmReadonly]);
               uuType:Type_Stmt([dmPrivate,dmExtentedType,dmPtrDcl,dmArrayDcl]);
               uuNone:break;
          else
              raise ECompException.Create('error '+TokenName(CurrentToken));
          end;
          NextToken();
       except on e:ECompException do
          begin
             Msg_Report(msError,e.Message);
             ErrorSync();
          end;
       end;
    until False;
    FStacks.Pop();
end;

procedure TUnitComp.CompileSection;
begin
    case State of
      ssHeaderSec:ProcessHeaderSection();
      ssSourceSec:ProcessSourceSection();
       ssCompiled:Exit;
    end;
    State:=ssCompiled;
end;

procedure TUnitComp.UsesStmt;
label ExitLab;
var
  ContinueUsesLoad:boolean;
begin
    ContinueUsesLoad := True;
    if not FLoadingUses then
    begin
         if TryNextToken(uuUsing) then
         begin
           FLoadingUses := True;
           ContinueUsesLoad := False;
         end else
              Exit;
    end;
    try
        NextToken();
        if ContinueUsesLoad then
          case CurrentToken of
                uuSep:NextToken;
            uuInstSep:goto ExitLab;
              uuIdent:Msg_Report(msError,@SEPARATOR_EXPECTED);
          end;
        repeat
          CheckCurrentToken(uuIdent);
          FMainComp.LoadUnit(GetTokenTxt(),FUnit);
          if State = ssCompiled then
             Exit;
          if NextToken()=uuIdent then
             Msg_Report(msError,@SEPARATOR_EXPECTED)
          else begin
             if CurrentToken<>uuSep then
                break;
             NextToken;
          end;
        until CurrentToken=uuInstSep;
 ExitLab:
    except on e:ECompException do
        begin
           Msg_Report(msError,e.Message);
           while not (NextToken()in [uuInstSep,uuNone ]) do;
        end;
    end;
    CheckCurrentToken(uuInstSep);
    FLoadingUses:=False;
end;

function TUnitComp.ExportUnitBin():integer;
var
 s,b:string;
 I,BuffSize:integer;
 Buff:TMemoryStream;
 UnitInf:TUnitInfo;
begin
   if FGenereted then
      Exit;
   if FUnit.FuncList.Count = 0then // no genered compiled
   begin
     if FImplPos<>-1 then
       with Tokens[FImplPos-1] do
         ProcesssedCode:=Copy(FCode,1,mPos+mLen);
     Exit;
   end;
   B:='';
   for I := 0 to FImplPos-1 do
      with Tokens[I] do
         b:=b+' '+Copy(FCode,mPos,mLen);
   Buff:=TMemoryStream.Create;
   try
       FGenerator.BinObj.SaveToStream(Buff);
       BuffSize :=Buff.Size;
       Buff.Write(PChar(b)^,length(b));
       Result := UCrc32.HashCRC32(Buff);
       Buff.Size := BuffSize;
       Buff.Write(Result,SizeOf(Result));
       if FGenereted then
       begin
           if FGenerator.BinObj.Version <>Result then
              raise ECompException.Create('crc error ');
           with FGenerator.BinObj do
            for I:= 0 to UnitsRefs.Count -1 do
            begin
              UnitInf :=TUnitInfo(UnitsRefs[I]);
              FMainComp.CheckLoadedUnit(UnitInf);
            end;
       end;
       FGenerator.BinObj.Version := Result;

       SetLength(s,Buff.size*2);
       BinToHex(PChar(Buff.Memory),PChar(s),Buff.size);
       b:=b+' link "'+s+'"';
       ProcesssedCode := b;
   finally
      Buff.Free;
   end;
end;

{ TMainComp }

constructor TMainComp.Create(const AName:string);
begin
   inherited Create(Self,AName);
   _CompList:=TQSList.Create;
   CompsNames:=TScope.Create;
end;

destructor TMainComp.Destroy;
begin
  _CompList.Free;
  CompsNames.Free;
  inherited;
end;

procedure TMainComp.CreateUnit;
begin
  FUnit :=TMainUnit.Create;
  FUnit.Name := Name;
  FUnit.DefaultVisibility :=vsPrivate;
end;

function TMainComp.LoadedUnits(ATag:integer):TUnitComp;
var
 Sym:TSymIdent;
begin
   Sym := CompsNames.Symbols[ATag];
   Result :=TUnitComp(Sym.Value.vPtr);
end;

function TMainComp.Comps(idx:integer):TComp;
begin
   Result :=TComp(_CompList[idx]);
end;

procedure TMainComp.UsesStmt();
begin
    if TryNextToken(uuUsing) then
    begin
        try
            NextToken();
            repeat
              CheckCurrentToken(uuIdent);
              FMainComp.LoadUnit(GetTokenTxt(),FUnit);
              if NextToken()=uuIdent then
                 Msg_Report(msError,@SEPARATOR_EXPECTED)
              else begin
                 if CurrentToken<>uuSep then
                    break;
                  NextToken;
              end;
            until CurrentToken=uuInstSep;
        except on e:ECompException do
            begin
               Msg_Report(msError,e.Message);
               while not (NextToken()in [uuInstSep,uuNone ]) do;
            end;
        end;
        CheckCurrentToken(uuInstSep);
    end;
end;

procedure TMainComp.CompileSection;
begin
    UsesStmt();
    FStacks.Push(TObject(esMain),[ssActiveErrSync]);
    NextToken();
    repeat
       try
          case CurrentToken of
               uuFunc:Func_Stmt([]);// dmPrivate default visibility
              uuConst:Const_Stmt([dmPrivate]);
             uuStatic:Var_Stmt([dmPrivate,dmStatic]);
           uuReadonly:Var_Stmt([dmPrivate,dmStatic,dmReadonly]);
               uuType:Type_Stmt([dmPrivate,dmExtentedType,dmPtrDcl,dmArrayDcl]);
               uuNone:break;
          else
             raise ECompException.Create('error '+TokenName(CurrentToken));
          end;
          NextToken();
       except on e:ECompException do
          begin
             Msg_Report(msError,e.Message);
             ErrorSync();
          end;
       end;
    until False;
    FStacks.Pop();
end;

procedure TMainComp.LoadUnit(const AName: string;ADest:TBaseUnit);
var
 C:TUnitComp;
 U:TUnit;
 Sym:TSymIdent;
begin
  if CompsNames.FindMember(AName,Sym) then
  begin
      C:=TUnitComp(Sym.Value.vPtr);
      U :=C.FUnit as TUnit;
      ADest.AddUnit(U);
      C.CompileSection();
  end else begin
      C:=TUnitComp.Create(Self,AName);
      C.FUnit.Address := CompsNames.Count;
      Sym :=CompsNames.NewSymbol(AName,TSymIdent);
      Sym.Value.vPtr := C;
      FfreeList.Add(C);
      ADest.AddUnit(C.FUnit as TUnit);
      try
          C.Parse(LoadUnitCode(AName,C));
          C.StartDecls();
          C.GetNextTokenAndCheck(uuNone);
          C.ExportUnitBin();
          c.FGenereted := True;
          SaveUnitCode(AName,C.ProcesssedCode);
      except
          on e:ECompException do
            C.Msg_Report(msError,e.Message);
      end;
  end;
end;

procedure TMainComp.CheckLoadedUnit(UnitInfo:TUnitInfo);
var
 Ver:integer;
 Comp:TComp;
 Sym:TSymIdent;
begin
   if CompsNames.FindMember(UnitInfo.Name,Sym) then
   begin
      Comp :=TUnitComp(Sym.Value.vPtr);
      Ver := Comp.FGenerator.BinObj.Version;
      if UnitInfo.Version <> Ver then
         raise ECompException.Create('crc error '+UnitInfo.Name);
   end else begin
      raise ECompException.Create('unfound '+UnitInfo.Name);
   end
end;

procedure TMainComp.AllocateUnit(BinObj:TBinObj);
var
 I:integer;
 Uinf:TUnitInfo;
 Comp:TComp;
 Sym:TSymIdent;
begin
  for I:=0 to  BinObj.UnitsRefs.Count-1 do
  begin
     Uinf:=TUnitInfo(BinObj.UnitsRefs[I]);
     if CompsNames.FindMember(Uinf.Name,Sym) then
     begin
        Comp :=TUnitComp(Sym.Value.vPtr);
        Uinf.Link := Comp.FGenerator.BinObj;
     end else begin
        if SameText(FUnit.Name,Uinf.Name) then
           Uinf.Link := FGenerator.BinObj
        else
           raise ECompException.Create('unfound '+Uinf.Name);
     end
  end;
end;

function  TMainComp.FindPatchedSym(AExpr: TExpr):TObjSymInfo;
var
 cUnit:TComp;
 Idx:integer;
begin
   idx   := AExpr.Address and $FFFF;
   cUnit := FMainComp.GetExprUnit(AExpr);
   Result := cUnit.FGenerator.BinObj.GlobalSymbs.GetSymbTag(idx);
end;

procedure TMainComp.Alloc_(AComp:TComp;AStream:TStream);
var
 I,J:integer;
 sf:TObjSymInfo;
 Expr,D,Nd:TExpr;
 Ds:TResBucket;
 sn:single;
 Dummy:int64;
 List:TExprList;
 procedure WriteExpr(AExpr:TExpr);
 begin
    if AExpr.xOp=imTextStream then
    begin
       Ds:= TResBucket(AExpr.Value.vPtr);
       AStream.Write(Ds.Data^,AExpr.DataType.TypeSize);
    end else if IsPtrLink(AExpr) then
    begin
       D := TOprExpr(AExpr).Expr1;
       with FindPatchedSym(D)do
       begin
            Dummy:= Value;
            if D.xOp = imOffset then
               Dummy:= Value+TOprExpr(D).Expr2.Value.vInt;
            AStream.Write(Dummy,AExpr.DataType.TypeSize);
       end;
    end else if AExpr.DataType.IsFloatType then
    begin
       sn := AExpr.AsNumber;
       AStream.Write(sn,AExpr.DataType.TypeSize)
    end else
       AStream.Write(AExpr.Value^,AExpr.DataType.TypeSize)
 end;
begin
  with AComp.FGenerator.BinObj do
   for I := 0 to GlobalSymbs.Count-1 do
   begin
      sf:=TObjSymInfo(GlobalSymbs[I]);
      if (sf.Loc = vtStatic)then
      begin
          Expr:= AComp.GetSymByTag(sf.Index);
          if Expr.Value.vPtr=nil then
          begin
             Dummy:=0;
             AStream.Write(Dummy,Expr.DataType.TypeSize);
             continue;
          end;
          Nd := TExpr(Expr.Value.vPtr);
          case  Nd.xOp of
              imTextStream:begin
                   Ds:= TResBucket(Nd.Value.vPtr);
                   AStream.Write(Ds.Data^,Nd.DataType.TypeSize);
              end;
              imInitList:begin
                     List :=TInitializerExpr(Nd).Elements;
                      for J:= 0 to List.Count-1 do
                      begin
                         Nd:= List.GetExpr(J);
                         WriteExpr(Nd);
                      end;
                 end;
              else
                  WriteExpr(Nd);
          end;
      end;
   end;
end;

function TMainComp.Build():boolean;
var
 I:integer;
 StaticSize,CodeSize:integer;
 EnterSection:TObjsGenerator;
 Expr:TExpr;
begin
   if not FUnit.FindMember('main',MainFunc)or(not MainFunc.IsCode) then
      Err(@MAIN_EXPECTED);
   if not MainFunc.DataType.Dest.IsVoidType() then
      Err(@INVALID_MAIN_RET);
   Expr := MakeAbsolutIndex(MainFunc);
   StaticSize :=0;
   CodeSize :=0;

   EnterSection:=TObjsGenerator.Create(Self);
   with EnterSection do  // statrt up code
   begin
       BinObj.NewFuncEntry;
       BinObj.GlobalSymbs.SymbTag(MainFunc.Address,0,vtCode);
       BinObj.Locals.EntryTag :=MainFunc.Address;
       PushResultAddr(Expr);
       LoadAddr(Expr,rgReg1);
       BinObj.NewInstruction(bcCall);
       BinObj.NewInstruction(bcHalt);
   end;
   AllocateUnit(EnterSection.BinObj);
   for I := 0 to _CompList.Count-1 do
     with Comps(I).FGenerator do
       AllocateUnit(BinObj);
   EnterSection.BinObj.UpdateLabsAndFuncs(CodeSize);
   for I := 0 to _CompList.Count-1 do
    with Comps(I) do
    begin
      TxtVersion := TSynEdit(Data).TextVersion;
      FGenerator.BinObj.CalcStaticVars(StaticSize);
      FGenerator.BinObj.UpdateLabsAndFuncs(CodeSize);
    end;
   OutputStream.Write(StaticSize,SizeOf(Integer));
   for I := 0 to _CompList.Count-1 do
       Alloc_(Comps(I),OutputStream);
   EnterSection.BinObj.LinkAndExport(OutputStream);
   for I := 0 to _CompList.Count-1 do
     with Comps(I) do
        FGenerator.BinObj.LinkAndExport(Self.OutputStream);
   Result := ErrorsCount =0;
   if not Result then
      OutputStream.Size :=0;

end;

function TMainComp.GetExprUnit(AExpr: TExpr): TComp;
var
  UnitIdx:integer;
begin
  if not (AExpr.ObjLocation in [olStatic,olCode,olType]) then
     raise ECompException.Create('invalid expr');
  UnitIdx := Smallint(AExpr.Address shr 16);
  if UnitIdx <> -1 then
     Result :=LoadedUnits(UnitIdx)
  else
     Result :=Self;
end;

{ TGenerator }

constructor TIRGenerator.Create(AComp: TComp);
begin
  FComp :=AComp;
  FLabels:=TList.Create;
  _TmpLabs:=TList.Create;
end;

destructor TIRGenerator.Destroy;
begin
  FLabels.Free;
  _TmpLabs.Free;
  inherited;
end;

function TIRGenerator.NewLabel: integer;
begin
  Result:=_TmpLabs.Add(nil);
end;

function TIRGenerator.NewTemp(dt:TDataType):TExpr;
begin
   if dt.IsStructArrayType then
      FComp.Msg_Report(msError,'struct or array forbiden',FActiveStmt.Line);
   Result := FActiveFunc.NewSymbol(TSymIdent);
   Result.SetDataType(dt);
   FActiveFunc.Allocate(Result);
   Result.ObjLocation := olTemp;
   if Assigned(FActiveStmt) then
    //  Result.Line :=FActiveStmt.Line;
end;

function TIRGenerator.GetLabAsGraph(ALab: integer): TGraphRec;
begin
  Result :=_TmpLabs[ALab];
  if Result =nil then
     raise ECompException.Create('GetLabAsGraph');
end;

function TIRGenerator.NewGraph():integer;
begin
  Result := NewLabel();
  EmitLabel(Result);
end;

procedure TIRGenerator.EmitLabel(ALab:integer);
var
 Grf:TGraphRec;
begin
    Grf :=FActiveGraph;
    FActiveGraph := TGraphRec.Create;
    FActiveGraph.FLabel:=FLabels.Add(nil);
    FGraphsList.Add(FActiveGraph);
    if Grf <> nil then
       Grf.LeftGraph:=FActiveGraph;
  _TmpLabs[ALab]:=FActiveGraph;
end;

procedure TIRGenerator.Jump(ALab:integer);
begin
  Gen(ir_GoTo,FComp.NewLiteralExpr(ALab),nil);
  NewGraph();
end;

procedure TIRGenerator.AddIR(O:TCompNode);
begin
  FActiveGraph.AddIRCode(O);
end;

procedure TIRGenerator.Gen(Op:TQsCmdInst;A1,A2:TExpr);
var
 N:TExpr;
begin
   N:=FComp.NewExpr(Op,A1,A2);
   AddIR(N);
   if FActiveStmt<> nil then
   begin
      N.Line:= FActiveStmt.Line;
   end;
end;

procedure TIRGenerator.CodeGen(AList:TStrings);
var
 I,J,n,Line:integer;
 Sym:TFuncBlockStmt;
 Cl:boolean;
 IR:TCompNode;
 C:TGraphSection;
 Grph:TGraphRec;
 Editor:TSynEdit;
begin
  Line := 0;
  Editor :=TSynEdit(FComp.Data);
  Editor.Compiled := False;
  Editor.ClearLinesInfos();
  for I:=0 to FComp.FUnit.FuncList.Count-1 do
  begin
       Sym := FComp.FUnit.FuncList[I];
       FuncVisit(TFuncBlockStmt(Sym));
       C :=TBlockStmt(TFuncBlockStmt(Sym).Code).Graphs;
       for n:= 0 to C.Count-1 do
       begin
         Grph:=C[n];
         for j :=0 to  Grph.FIRList.Count -1 do
         begin
            IR :=Grph.FIRList[j];
            if IR.Line <>0 then
            begin
               if IR.xOp=ir_call then
                  Editor.SetLineProps(IR.Line,[inf_ExecLine,Inf_CallLine])
               else
                  Editor.SetLineProps(IR.Line,[inf_ExecLine])
            end else
                  Editor.ResetLineProps(IR.Line,[inf_ExecLine,Inf_CallLine])
         end;
       end;

       if AList=nil then
         continue;

       Cl:=false;

       C :=TBlockStmt(TFuncBlockStmt(Sym).Code).Graphs;
       for n:= 0 to C.Count-1 do
       begin
         Grph:=C[n];
         if  Grph.FIRList.Count =0 then
            continue;
         for j :=0 to  Grph.FIRList.Count -1 do
         begin
            IR :=Grph.FIRList[j];
            AList.AddObject(format('%3.3d %s',[Line,IRToString(IR)]),Pointer(Cl));
            inc(Line);
         end;
         Cl := not Cl;
       end;
  end;
  Editor.Compiled := True;
end;

procedure TIRGenerator.FuncVisit(AFuncBlock:TFuncBlockStmt);
var
 I,J:integer;
 Grph:TGraphRec;
 IR:TCompNode;
 Stmt:TBlockStmt;
 Expr:TOprExpr;
begin
  FActiveFunc :=AFuncBlock;
  Stmt :=TBlockStmt(AFuncBlock.Code);
  FGraphsList := Stmt.Graphs;
  FActiveGraph := nil ;
  FActiveStmt :=nil;
  StmtVisit(Stmt);
  StmtGen(AFuncBlock.Epilogue);
  for I:= 0 to FGraphsList.Count-1 do
  begin
     Grph:=FGraphsList[I];
     for j :=0 to  Grph.FIRList.Count -1 do
     begin
        IR :=Grph.FIRList[j];
        case IR.xOp of
             ir_IfFalse,ir_RelOp:begin
                Expr:=TOprExpr(TOprExpr(IR).Expr1);
                Grph.LeftGraph  :=GetLabAsGraph(Expr.Expr1.Value.vInt);
                Grph.RightGraph :=GetLabAsGraph(Expr.Expr2.Value.vInt);
                Expr.Expr1.Value.vInt := Grph.LeftGraph .FLabel;
                Expr.Expr2.Value.vInt := Grph.RightGraph .FLabel;
             end;
             ir_GoTo:begin
                Expr:=TOprExpr(IR);
                Grph.LeftGraph :=GetLabAsGraph(Expr.Expr1.Value.vInt);
                Expr.Expr1.Value.vInt :=Grph.LeftGraph.FLabel;
             end;
           ir_TryEnter:begin
                Expr:=TOprExpr(IR);
                Grph.LeftGraph  :=GetLabAsGraph(Expr.Expr1.Value.vInt);
                Grph.RightGraph :=GetLabAsGraph(Expr.Expr2.Value.vInt);
                Expr.Expr1.Value.vInt := Grph.LeftGraph .FLabel;
                Expr.Expr2.Value.vInt := Grph.RightGraph .FLabel;
            end;
     __TrySecLink:begin
                Expr:=TOprExpr(IR);
                Grph.LeftGraph  :=GetLabAsGraph(Expr.Expr1.Value.vInt);
                Grph.RightGraph :=GetLabAsGraph(Expr.Expr2.Value.vInt);
            end;
     ir_Throw:begin
                Grph.LeftGraph  :=nil;
                Grph.RightGraph :=nil;// not need
            end;
       end;
     end;
  end;
  BuidGraph();
  for I:= 0 to FGraphsList.Count-1 do
  begin
     Grph:=FGraphsList[I];
     for j :=0 to  Grph.FIRList.Count -1 do
     begin
        IR :=Grph.FIRList[j];
        case IR.xOp of
             ir_GoTo:begin
                with TOprExpr(IR).Expr1 do
                     Value.vInt :=integer(FLabels[Value.vInt]); //  ****
              end;
           ir_IfFalse,ir_RelOp:begin
               Expr:=TOprExpr(TOprExpr(IR).Expr1);
               Expr.Expr1.Value.vInt :=integer( FLabels[Expr.Expr1.Value.vInt]);
               Expr.Expr2.Value.vInt :=integer( FLabels[Expr.Expr2.Value.vInt]);
             end;
         ir_TryEnter:begin
               Expr:=TOprExpr(IR);
               Expr.Expr1.Value.vInt :=integer( FLabels[Expr.Expr1.Value.vInt]);
               Expr.Expr2.Value.vInt :=integer( FLabels[Expr.Expr2.Value.vInt]);
            end;
        end;
     end;
  end;
  _LivenessAnalyse(); // must be first
  InitializationAnalyse();
end;

procedure TIRGenerator._LivenessAnalyse();
var   // try /finally needs some special operations
 I,J:integer;
 Grph:TGraphRec;
 IR:TCompNode;
 Expr:TOprExpr;
begin
  for I:= 0 to FGraphsList.Count-1 do
  begin
     Grph:=FGraphsList[I];
     for j :=0 to  Grph.FIRList.Count -1 do
     begin
        IR :=Grph.FIRList[j];
        case IR.xOp of
          __TrySecLink:begin
               //used only for livness analyse
               Grph.RightGraph :=nil;
            end;
          ir_FinallyRet:begin
                Expr:=TOprExpr(IR);
                Grph.LeftGraph  :=GetLabAsGraph(Expr.Expr1.Value.vInt);
            end;
        end;
     end;
  end;
  FGraphsList.BuildInterLinks();
  LivenessAnalyse();
  for I:= 0 to FGraphsList.Count-1 do
  begin
     Grph:=FGraphsList[I];
     for j :=0 to  Grph.FIRList.Count -1 do
     begin
        IR :=Grph.FIRList[j];
        case IR.xOp of
          __TrySecLink:begin
               // transform to ir_Goto :used only for livness analyse
                Expr:=TOprExpr(IR);
                Grph.LeftGraph  := GetLabAsGraph(Expr.Expr2.Value.vInt) ;
                Expr.Expr1.Value.vInt :=integer( FLabels[ Grph.LeftGraph.FLabel ]);
                IR.xOp :=ir_Goto;
            end;
          ir_FinallyRet:begin
                Grph.LeftGraph  := nil;
            end;
        end;
     end;
  end;
  FGraphsList.BuildInterLinks();
end;

procedure TIRGenerator.GenCopy(Dest,Src:TExpr);
begin
   Gen(ir_Copy,Dest,Src);
end;

procedure TIRGenerator._JumpsExprVisit(AExpr:TExpr;ATrueLab,AFalseLab:integer);
var
 BinExpr:TOprExpr;
 Lab:integer;
 t1,t2,Expr,Labs:TExpr;
begin
   BinExpr :=TOprExpr(AExpr);
   case AExpr.xOp of
        imNot:_JumpsExprVisit(BinExpr.Expr1,AFalseLab,ATrueLab);
     imAndCmp:begin
             Lab := NewLabel();
             _JumpsExprVisit(BinExpr.Expr1,Lab,AFalseLab);
             EmitLabel(Lab);
             _JumpsExprVisit(BinExpr.Expr2,ATrueLab,AFalseLab);
         end;
     imOrCmp:begin
             Lab := NewLabel();
             _JumpsExprVisit(BinExpr.Expr1,ATrueLab,Lab);
             EmitLabel(Lab);
             _JumpsExprVisit(BinExpr.Expr2,ATrueLab,AFalseLab);
         end;
   else
      if AExpr.xOp in [imEqu,imLess,imGr,imNotequ,imLessEqu,imGrEqu,imIs] then
      begin
         t1 := ExprVisit(BinExpr.Expr1,False);
         t2 := ExprVisit(BinExpr.Expr2,False);
         Expr :=FComp.NewExpr(AExpr.xOp,t1,t2);
      end else begin
         Expr := ExprVisit(AExpr,False);
      end;
      if Expr.IsConstant then
      begin
         if Expr.Value.vBool then  // modified const switch
            Jump(ATrueLab)
         else
            Jump(AFalseLab)
      end else begin
         with FComp do
           Labs := NewExpr(imNone,NewLiteralExpr(ATrueLab),NewLiteralExpr(AFalseLab));
         case AExpr.xOp of
              imEqu,imLess,imGr,
           imNotequ,imLessEqu,imGrEqu,imIs:
                Gen(ir_RelOp,Labs,Expr);
         else
            Gen(ir_IfFalse,Labs,Expr);
         end;
         NewGraph();
      end;
   end;
end;

procedure TIRGenerator.JumpsExprVisit(AExpr:TExpr;AFalseLab:integer);
var
  TrueLab:integer;
begin
   TrueLab := NewLabel();
   _JumpsExprVisit(AExpr,TrueLab,AFalseLab);
   EmitLabel(TrueLab);
end;

function TIRGenerator.JumpsToBool(AExpr:TExpr):TExpr;
var
 L1,L2:integer;
begin
   L1:=NewLabel();
   L2:=NewLabel();
   Result :=NewTemp(AExpr.DataType);
   JumpsExprVisit(AExpr,L1);
   GenCopy(Result,FComp.NewLiteralExpr(True));
   Jump(L2);
   Emitlabel(L1);
   GenCopy(Result,FComp.NewLiteralExpr(False));
   Emitlabel(L2);
end;

function TIRGenerator.OpExprVisit(AExpr:TExpr):TExpr;
var
 BinExpr:TOprExpr;
 t1,t2:TExpr;
begin
   Result :=NewTemp(AExpr.DataType);
   BinExpr :=TOprExpr(AExpr);
   t1 :=ExprVisit(BinExpr.Expr1,False);
   t2 :=ExprVisit(BinExpr.Expr2,False);
   Gen(ir_BinOp,Result,FComp.NewExpr(AExpr.xOp,t1,t2 ));
end;

function TIRGenerator.ExprVisit(AExpr:TExpr;LValue:boolean):TExpr;
var
 BinExpr:TOprExpr;
 TerExpr:TOprExpr;
 L1,L2:integer;
 t,t1,t2:TExpr;
begin
   Result :=AExpr;
   case AExpr.xOp of
    imInvocation: Result :=  Call_Visit(TFunctionCallExpr(AExpr));
    imAndCmp,imOrCmp,imNot,
    imEqu,imLess,imGr,imNotequ,imLessEqu,imGrEqu,imIs: Result := JumpsToBool(AExpr);
    imAdd,imSub,imMul,imDiv,imModul,
    imAnd,imOr,imXor,imShl,imShr: Result := OpExprVisit(AExpr);
    imAssign:begin
           BinExpr :=TOprExpr(AExpr);
           t1 := ExprVisit(BinExpr.Expr1,True);
           t2 := ExprVisit(BinExpr.Expr2,False);
           GenCopy(t1,t2);
           Result :=t1;
           if not LValue then
           begin
              t :=NewTemp(BinExpr.Expr2.DataType);
              GenCopy(t,Result);
              Result :=t;
           end;
     end;
    imOffset:begin
           BinExpr :=TOprExpr(AExpr);
           if (BinExpr.Expr1.DataType.IsTypedPointer)or not LValue then
              t1 := ExprVisit(BinExpr.Expr1,False)
           else
              t1 := ExprVisit(BinExpr.Expr1,True);
           t2 := ExprVisit(BinExpr.Expr2,False);
           Result :=FComp.NewExpr(imOffset,t1,t2);
           Result.Assign(AExpr);
           if not LValue then
           begin
               t :=NewTemp(AExpr.DataType);
               GenCopy(t,Result);
               Result :=t;
           end;
     end;
    imImplicit,imExplicit:begin
             Result:=ExprVisit(TOprExpr(AExpr).Expr1,False);
             t := NewTemp(AExpr.DataType);
             if Result.IsMethod()and AExpr.DataType.IsMethodType then // method
             with TOprExpr(Result)do
             begin
                t1:= FComp.NewOffsetExpr(t,FComp.NewLiteralExpr(0),PtrType.DataType);
                t2:= ExprVisit(Expr1,False);
                GenCopy(t1,t2);
                t1:= FComp.NewOffsetExpr(t,FComp.NewLiteralExpr(SIZEOFPOINTER),PtrType.DataType);
                t2:= ExprVisit(Expr2,False);
                GenCopy(t1,t2);
             end else begin// ir_DynamicCast
                GenCopy(t,Result);
             end;
             Result :=t;
          end;
    imAs:begin// ir_DynamicCast
              Result:=ExprVisit(TOprExpr(AExpr).Expr1,False);
              t := NewTemp(AExpr.DataType);
              Gen(ir_DynamicCast,t,Result);
              Result:=t;
           end;
    __NodeTypeConvert:begin
              t:=ExprVisit(TOprExpr(AExpr).Expr1,False);
              Result := FComp.NewExpr(); // not a temp var :type conv
              Result.Assign(t);
              Result.SetDataType(AExpr.DataType);
           end;
    imTest:begin
          Result :=NewTemp(AExpr.DataType);
          BinExpr := TOprExpr(AExpr); // test Expr
          TerExpr := TOprExpr(BinExpr.Expr2);
          L1:=NewLabel();
          L2:=NewLabel();
          JumpsExprVisit(BinExpr.Expr1,L1);
          t1 := ExprVisit(TerExpr.Expr1,False);
          GenCopy(Result,t1);
          Jump(L2);
          EmitLabel(L1);
          t2 := ExprVisit(TerExpr.Expr2,False);
          GenCopy(Result,t2);
          EmitLabel(L2);
     end;
   imAddr:begin
          Result :=NewTemp(AExpr.DataType);
          t:=ExprVisit(TOprExpr(AExpr).Expr1,True);
          Gen(ir_Addr,Result,FComp.NewExpr(AExpr.xOp,t,nil));
     end;
   imMinus,imComp:begin
          Result :=NewTemp(AExpr.DataType);
          t:=ExprVisit(TOprExpr(AExpr).Expr1,False);
          Gen(ir_UnOp,Result,FComp.NewExpr(AExpr.xOp,t,nil));
     end;
   imDeref:begin
          t:=ExprVisit(TOprExpr(AExpr).Expr1,False);
          Result :=FComp.NewExpr(imDeref,t,nil);
          Result.Assign(AExpr);
          if not LValue then
          begin
             t :=NewTemp(AExpr.DataType);
             GenCopy(t,Result);
             Result :=t;
          end;
     end;
   imRef:begin
          t:=ExprVisit(TOprExpr(AExpr).Expr1,False);
          Result :=FComp.NewExpr(imDeref,t,nil);
          Result.Assign(TOprExpr(AExpr).Expr2);
         // Result.Index := t.Index;
         // Result.Assign(AExpr);
        //  Result.ObjLocation :=  TOprExpr(AExpr).Expr2.Index;
        //  Result.ObjLocation :=  TOprExpr(AExpr).Expr2.Index;
          if not LValue then
          begin
             t :=NewTemp(AExpr.DataType);
             GenCopy(t,Result);
             Result :=t;
          end;
     end;
   imPreInc,imPreDec:
     begin
          BinExpr := TOprExpr(AExpr);
          t1:=ExprVisit(BinExpr.Expr1,True);
          t2:=ExprVisit(BinExpr.Expr2,False); // inc by //factor
          Result:=t1;
          case AExpr.xOp of
             imPreInc: Gen(ir_Inc,Result,t2);
             imPreDec: Gen(ir_Dec,Result,t2);
          end;
          if not LValue then   // cree une temp pour eviter : m[p]++
          begin
             t :=NewTemp(AExpr.DataType);
             GenCopy(t,Result);
             Result :=t;
          end else begin   // for graph analys
             t :=NewTemp(AExpr.DataType);
             GenCopy(t,Result);
            // Result :=t;
          end;
     end;
   imPostInc,imPostDec:
     begin
          Result :=NewTemp(AExpr.DataType);
          BinExpr := TOprExpr(AExpr);
          t1:=ExprVisit(BinExpr.Expr1,True);
          t2:=ExprVisit(BinExpr.Expr2,False); // inc by //factor
          GenCopy(Result,t1);
          case AExpr.xOp of
             imPostInc: Gen(ir_Inc, t1,t2);
             imPostDec: Gen(ir_Dec, t1,t2);
          end;
     end;
   imConstructor:begin
          Result := AExpr; // do not alloc temp var :yet alloued in NewConstructor
          t := TOprExpr(AExpr).Expr1;
          Gen(imConstructor,Result,t);
          ExprVisit(TOprExpr(AExpr).Expr2,True); // call initialier
      end;
  end;
end;

function TIRGenerator.Call_Visit(ACall:TFunctionCallExpr):TExpr;
var
  I:integer;
  Expr,t,Func:TExpr;
  InstanceExpr,vTable:TExpr;
begin
   Result:=NewTemp(ACall.DataType);
   Func := ExprVisit(ACall.FuncInst,False);
   InstanceExpr := nil;
   vTable := nil;
   if ACall.ObjInstance<>nil then
   begin
     InstanceExpr := ExprVisit(ACall.ObjInstance,False);
     if TSymIdent(Func).IsVirtualFunc then
        vTable := InstanceExpr;
   end else if Func.DataType.IsMethodType then
   begin// call from var
     InstanceExpr := FComp.NewOffsetExpr(Func,FComp.NewLiteralExpr(0),PtrType.DataType);
             Func := FComp.NewOffsetExpr(Func,FComp.NewLiteralExpr(SIZEOFPOINTER),PtrType.DataType);
   end;
   for I:= ACall.ConvArgList.Count-1 downto 0 do  //stdcall conv
   begin
      Expr :=ACall.ConvArgList.GetExpr(I);
      t := ExprVisit(Expr,False);
      Gen(ir_LoadParam, t, nil);
   end;
   if InstanceExpr <> nil then
   begin
      Gen(ir_LoadParam, InstanceExpr, nil);
   end;
   Gen(ir_Call,FComp.NewExpr(imNone,Result,Func),vTable);
end;

procedure TIRGenerator.FuncBlockVisit(AStmt:TBlockStmt);
begin
  EmitLabel(AStmt.StartLab);
  StmtVisit(AStmt.S);
  EmitLabel(AStmt.EndLab);
  
 // Gen(ir_Ret, nil,nil);
end;

procedure TIRGenerator.StmtCreateLabels(AStmt:Pointer);
begin
   with TStmt(AStmt) do
   begin
      StartLab := NewLabel();
      EndLab   := NewLabel();
   end;
   if  TStmt(AStmt).xOp in [imWhileStmt,imDoStmt,imForStmt,
                            imSwitchStmt,imFinallyStmt,imCatchStmt] then
     with TLoopStmt(AStmt) do
     begin
        ContinueLab := NewLabel();
        BreakLab := NewLabel();
     end;
end;

procedure TIRGenerator.StmtGen(AStmt:Pointer);
begin
   FActiveStmt:=AStmt;
   case TStmt(AStmt).xOp of
         imExprStmt:ExprStmt_Visit(AStmt);
           imIfStmt:If_Visit(AStmt);
        imWhileStmt:While_Visit(AStmt);
           imDoStmt:Do_Visit(AStmt);
          imForStmt:For_Visit(AStmt);
         imListStmt:StmtList_Visit(AStmt);
         imGoToStmt:GoTo_Visit(AStmt);
        imLabelStmt:LabelStmt_Visit(AStmt);
       imReturnStmt:Return_Visit(AStmt);
        imBreakStmt:Break_Visit(AStmt);
     imContinueStmt:Continue_Visit(AStmt);
     imExprInitStmt:ExprInitStmt_Visit(AStmt);
       imSwitchStmt:SwitchStmt_Visit(AStmt);
        imBlockStmt:FuncBlockVisit(AStmt);
        imPrintStmt:Print_Visit(AStmt);
      imFinallyStmt:TryFinally_Visit(AStmt);
       imCatchStmt:TryExcept_Visit(AStmt);
        imThrowStmt:Throw_Visit(AStmt);
     imFuncEpilogue:Gen(ir_Ret, nil,nil);
   end;
  // FActiveStmt:=nil;
end;

procedure TIRGenerator.StmtVisit(AStmt:Pointer);
begin
   if AStmt = nil then
      Exit;
   StmtCreateLabels(AStmt);
   StmtGen(AStmt);
end;

procedure TIRGenerator.ExprStmt_Visit(AStmt:TExprStmt);
begin
   ExprVisit(AStmt.Expr,True);
end;

procedure TIRGenerator.If_Visit(AStmt:TIfStmt);
var
 L1,L2:integer;
begin
   L1:=NewLabel();
   L2:=L1;
   JumpsExprVisit(AStmt.Cond,L2);
   StmtVisit(AStmt.TrueStmt);
   if AStmt.FalseStmt <> nil then
   begin
      L2:=NewLabel();
      Jump(L2);
      EmitLabel(L1);
      StmtVisit(AStmt.FalseStmt);
   end;
   EmitLabel(L2);
end;

procedure TIRGenerator.While_Visit(AStmt:TWhileStmt);
begin
   EmitLabel(AStmt.ContinueLab);
   JumpsExprVisit(AStmt.Cond,AStmt.BreakLab);
   StmtVisit(AStmt.Stmt);
   Jump(AStmt.ContinueLab);
   EmitLabel(AStmt.BreakLab);
end;

procedure TIRGenerator.Do_Visit(AStmt:TDoStmt);
var
  LoopLabel:integer;
begin
   LoopLabel := NewLabel();
   EmitLabel(LoopLabel);
   StmtVisit(AStmt.Stmt);
   EmitLabel(AStmt.ContinueLab);
   JumpsExprVisit(AStmt.Cond,AStmt.BreakLab);
   Jump(LoopLabel);
   EmitLabel(AStmt.BreakLab);
end;
    
procedure TIRGenerator.For_Visit(AStmt:TForStmt);
var
  LoopLabel:integer;
begin
    LoopLabel := NewLabel();
    StmtVisit(AStmt.InitExpr);
    EmitLabel(LoopLabel);
    if AStmt.CondExpr<> nil then
      JumpsExprVisit(AStmt.CondExpr,AStmt.BreakLab);
    StmtVisit(AStmt.S);
    EmitLabel(AStmt.ContinueLab);
    StmtVisit(AStmt.ExprsOpt);
    Jump(LoopLabel);
    EmitLabel(AStmt.BreakLab);
end;

procedure TIRGenerator.TryFinally_Visit(AStmt:TTryHandler);
var
   FinallyLab,ExecLab:TExpr;
   L:integer;
   Gr1,Gr2:TGraphRec;
begin
   L:=Newlabel();
   StmtCreateLabels(AStmt.Handler.S);
   StmtCreateLabels(AStmt.Exec.S);
   ExecLab    := FComp.NewLiteralExpr(AStmt.Exec.S.StartLab);
   FinallyLab := FComp.NewLiteralExpr(AStmt.Handler.S.StartLab);
   Gen(ir_TryEnter,ExecLab,FinallyLab);
   EmitLabel(AStmt.Exec.S.StartLab);// split current graph
   Gr1:= FActiveGraph;
   StmtGen(AStmt.Exec.S);
   FActiveStmt :=AStmt.Handler.S;
   Gen(ir_ExitFinally,nil,nil);
   Newgraph();
   Gen(__TrySecLink,FComp.NewLiteralExpr(AStmt.Handler.S.StartLab),
                     FComp.NewLiteralExpr(L));
   EmitLabel(AStmt.Handler.S.StartLab);
   Gr2:= FActiveGraph;
   StmtGen(AStmt.Handler.S);
   FActiveStmt :=AStmt._EndHandler;
   Gen(ir_FinallyRet,FComp.NewLiteralExpr(L),nil);
   EmitLabel(L);
   Gen(__TryEnd,FComp.NewLiteralExpr(Gr1),FComp.NewLiteralExpr(Gr2));
   NewGraph();
end;

procedure TIRGenerator.TryExcept_Visit(AStmt:TTryHandler);
var
   FinallyLab,ExecLab:TExpr;
   I,Next:integer;
   SList:TStmtList;
   CatchStmt:TCaseStmt;
   t,ErrExpr:TExpr;
   St:TSimpleStmt;
begin
   Next := NewLabel();
   StmtCreateLabels(AStmt.Handler.S);
   StmtCreateLabels(AStmt.Exec.S);
   ExecLab    := FComp.NewLiteralExpr(AStmt.Exec.S.StartLab);
   FinallyLab := FComp.NewLiteralExpr(AStmt.Handler.S.StartLab);
   Gen(ir_TryEnter,ExecLab,FinallyLab);
   EmitLabel(AStmt.Exec.S.StartLab);
   StmtGen(AStmt.Exec.S);
   ExitTry(AStmt);
   Jump(Next);
   EmitLabel(AStmt.Handler.S.StartLab);
   FActiveStmt :=AStmt.Handler.S;
   SList := TStmtList(AStmt.Handler.S);
   ErrExpr := NewTemp(IntType.DataType);
   Gen(ir_ErrRead,ErrExpr,nil);
   for I := 0 to SList.List.Count-1 do
   begin
      CatchStmt := SList.List[I];
      St:=TSimpleStmt(CatchStmt.S);
      StmtCreateLabels(St.S);
      with CatchStmt do
        begin
           t:= FComp.NewBinBaseExpr(imEqu,Value,ErrExpr);
           _JumpsExprVisit(t,St.S.StartLab,St.S.EndLab);
           EmitLabel(St.S.StartLab);
           Gen(ir_ExceptRet,FComp.NewLiteralExpr(True),nil);// handle error
           StmtGen(St.S);
           Gen(ir_POPErr,nil,nil);
           FActiveStmt :=AStmt._EndHandler;
           Jump(AStmt.Handler.S.EndLab); // do not exit to ir_ExceptRet
           EmitLabel(St.S.EndLab);
        end;
   end;
   if Assigned(AStmt.DefaultErrHandler) then
   begin
       St:=TSimpleStmt(TCaseStmt(AStmt.DefaultErrHandler).S);
       StmtCreateLabels(St.S);
       EmitLabel(St.S.StartLab);
       Gen(ir_ExceptRet,FComp.NewLiteralExpr(True),nil);// handle error
       StmtGen(St.S);
       Gen(ir_POPErr,nil,nil);
       Jump(AStmt.Handler.S.EndLab);
       EmitLabel(St.S.EndLab);
   end else begin
       Gen(ir_ExceptRet,nil,nil);// unhandled error
   end;
   EmitLabel(AStmt.Handler.S.EndLab);
   EmitLabel(Next);
end;

procedure TIRGenerator.Throw_Visit(AStmt:TExprStmt);
var
   err:TExpr;
begin
   err := nil;
   if AStmt.Expr <> nil then
   begin
      err:= ExprVisit(AStmt.Expr,False);
   end;
   NewGraph();
   Gen(ir_Throw,err,nil);
   NewGraph();
end;

procedure TIRGenerator.StmtList_Visit(AStmt:TStmtList);
var
  I:integer;
begin
   for I:= 0 to AStmt.List.Count-1 do
       StmtVisit(AStmt.List[I]);
end;

procedure TIRGenerator.GoTo_Visit(AStmt:TSimpleStmt);
var
 L:TLabelStmt;
begin
   L:=TLabelStmt(AStmt.S);
   if L.lab= nil then
   begin
      L.lab:=FComp.NewConstExpr();
      L.lab.Value.vInt :=Newlabel();
   end;
   Jump(L.lab.Value.vInt);
end;

procedure TIRGenerator.LabelStmt_Visit(AStmt:TLabelStmt);
begin
   if AStmt.lab= nil then
   begin
      AStmt.lab:=FComp.NewConstExpr();
      AStmt.lab.Value.vInt :=Newlabel();
   end;
   EmitLabel(AStmt.lab.Value.vInt);
   StmtVisit(AStmt.Stmt);
end;

procedure TIRGenerator.Break_Visit(AStmt:TStmt);
var
 LoopStmt:TLoopStmt;
begin
   LoopStmt:=LoopExitHandler(AStmt.StmtsJumps);
   Jump(LoopStmt.BreakLab);
end;

procedure TIRGenerator.Continue_Visit(AStmt:TStmt);
var
 LoopStmt:TLoopStmt;
begin
   LoopStmt:=LoopExitHandler(AStmt.StmtsJumps);
   Jump(LoopStmt.ContinueLab);
end;

procedure TIRGenerator.ExitTry(AStmt:TTryHandler);
begin
   if AStmt.xOp = imFinallyStmt then
      Gen(ir_ExitFinally,nil,nil)
   else {imCatchStmt }
      Gen(ir_ExitExcept,nil,nil);
  //  NewGraph();// next addr
end;

function TIRGenerator.LoopExitHandler(AStmt:TLoopStmt):TLoopStmt;
begin
   Result:=AStmt;
   while Result.xOp in[imFinallyStmt,imCatchStmt] do //is TTryHandler
   begin
      ExitTry(TTryHandler(Result));
      Result := TTryHandler(Result).ParentLoopStmt;
   end;
end;

procedure TIRGenerator.Return_Visit(AStmt:TReturnStmt);
var
 BinExpr :TOprExpr;
 t,ret:TExpr;
 TryHandler:TTryHandler;
begin
   if AStmt.xExprs<> nil then
   begin
      BinExpr :=TOprExpr(AStmt.xExprs);
      t:=ExprVisit(BinExpr.Expr2,False);
      ret :=ExprVisit(BinExpr.Expr1,True);
      GenCopy(ret,t);
   end;
   TryHandler:=AStmt.Handler;
   while TryHandler<>nil do
   begin
      ExitTry(TryHandler);
      TryHandler := TryHandler.ParentTryHandler;
   end;
   Jump(AStmt.CodeStmt.Code.EndLab);
end;

procedure TIRGenerator.ExprInitStmt_Visit(AStmt:TInitStmt);
var
 Expr:TExpr;
 List:TExprList;
 J,Offset:integer;
 Nd:TExpr;
 Ds:TResBucket;
 procedure WriteExpr(AExpr,ADest:TExpr);
 var
  t:TExpr;
  I:integer;
 begin
    if AExpr.xOp=imTextStream then
    begin
       Ds:= TResBucket(AExpr.Value.vPtr);
       for I := 0 to Ds.Size-1 do
       begin
          t:=FComp.NewOffsetExpr(AStmt.Dst,FComp.NewLiteralExpr(Offset+I),CharType.DataType);
          GenCopy(t,FComp.NewLiteralExpr(Ds.Data[I]));
       end;
    end else begin
        t := ExprVisit(AExpr,False);
        GenCopy(ADest,t);
    end;
 end;
begin
  Offset:=0;
  //AStmt.Src := ExprVisit(AStmt.Src,True);
  if AStmt.Src.xOp = imInitList then
  begin
      List :=TInitializerExpr(AStmt.Src).Elements;
      for J:= 0 to List.Count-1 do
      begin
        Nd:= List.GetExpr(J);
        Expr := FComp.NewOffsetExpr(AStmt.Dst,FComp.NewLiteralExpr(Offset),Nd.DataType);;
        WriteExpr(Nd,Expr);
        Offset:=Offset+Nd.DataType.TypeSize;
      end;
  end else
        WriteExpr(AStmt.Src,AStmt.Dst);
end;

procedure TIRGenerator.SwitchStmt_Visit(AStmt:TSwitchStmt);
var
  I,FalseLab:integer;
  CaseStmt:TCaseStmt;
  t,d:TExpr;
begin
   if not AStmt.xExpr.IsConstant then
   begin
      d := NewTemp(AStmt.xExpr.DataType);
      t := ExprVisit(TOprExpr(AStmt.xExpr).Expr1,False);
      GenCopy(d,t);
   end else
      d :=AStmt.xExpr;
   for I:=0 to AStmt.CasesList.List.Count-1 do
   begin
      CaseStmt:=TCaseStmt(AStmt.CasesList.List[I]);
      CaseStmt.StartLab := Newlabel();
      if CaseStmt.xExpr <> nil then
      begin
         FalseLab :=Newlabel();
         t:= FComp.NewBinBaseExpr(imEqu,CaseStmt.xExpr,d);
         _JumpsExprVisit(t,CaseStmt.StartLab,FalseLab);
         EmitLabel(FalseLab);
      end;
   end;
   if AStmt.DefaultStmt<> nil then
      Jump(AStmt.DefaultStmt.StartLab)
   else
      Jump(AStmt.BreakLab);
   for I:=0 to AStmt.CasesList.List.Count-1 do
   begin
      CaseStmt:=TCaseStmt(AStmt.CasesList.List[I]);
      EmitLabel(CaseStmt.StartLab);
      StmtGen(CaseStmt.S);
   end;
   EmitLabel(AStmt.BreakLab);
end;

procedure TIRGenerator.Print_Visit(AStmt:TPrintStmt);
var
 t:TExpr;
begin
  t := ExprVisit(AStmt.Expr,False);
  Gen(ir_Print,t,FComp.NewLiteralExpr(AStmt.ByRef));
end;

procedure TIRGenerator.BuidGraph();
var
  I:integer;
  Grf:TGraphRec;
  procedure VisitGraph(AGrph:TGraphRec); // dead code elimination
  begin
     if (AGrph =nil)or AGrph.UsedMark then
        Exit;
     AGrph.UsedMark:=True;//visited
     VisitGraph(AGrph.LeftGraph);
     VisitGraph(AGrph.RightGraph);
  end;
begin
    with TGraphSection.Create do
    try
         for i:= 0 to FGraphsList.Count-1 do
           Add(FGraphsList[I]);

         VisitGraph(items[0]);
         FGraphsList.Clear;

         for i:= 0 to Count-1 do
         begin
           Grf:=items[I];
           if Grf.UsedMark  then
           begin
              FLabels[Grf.FLabel] :=Pointer(Line);
              Line:= Line+Grf.FIRList.Count;
              Grf.Vars_In_Set := TBitsSet.Create(FActiveFunc.LocalsVarCount);
              Grf.Vars_Out_Set := TBitsSet.Create(FActiveFunc.LocalsVarCount);
              Grf._Set := TBitsSet.Create(FActiveFunc.LocalsVarCount);
              FGraphsList.Add(Grf);
           end;
         end;
     finally
        Free()
     end;
     FGraphsList.BuildInterLinks();
end;

procedure TIRGenerator.Report_NotUsed_Value(AExpr: TExpr;AIR:TCompNode);
begin
  FComp.Msg_Report(msNote,'value not used '+AExpr.Name,AIR.Line);
end;

procedure TIRGenerator.Report_uninitialized(AExpr: TExpr;AIR:TCompNode);
begin
  FComp.Msg_Report(msNote,'undefined '+AExpr.Name,AIR.Line);
end;

procedure TIRGenerator.GetUsedExprs(Vars:TBitsSet;AIR:TCompNode;ADest:TExpr);
var
 Exp1:TExpr;
 Exp2:TExpr;
 Exp3:TExpr;
 Exp4:TExpr;
begin
  Exp1 :=nil;
  Exp2 :=nil;
  Exp3 :=nil;
  Exp4 :=nil;
  with TOprExpr(AIR) do
    case xOp of
       ir_LoadParam:Exp1 :=Expr1;
       ir_Inc,ir_Dec:Exp1 :=Expr1;
             ir_Copy:begin
                     Exp1 :=Expr2;
          { if Expr2.xOp =imDeref then
             with TOprExpr(Expr2) do
             begin
                  Exp3 :=Expr1;
             end;

           if Expr1.xOp =imDeref then
             with TOprExpr(Expr1) do
             begin
                  Exp4 :=Expr1;
             end;  }
        end;
       ir_Call:
         with TOprExpr(Expr1) do
         begin
             Exp1 :=Expr2;
         end;
       ir_IfFalse:Exp1 :=Expr2;
       ir_RelOp:
         with TOprExpr(Expr2) do
         begin
             Exp1 :=Expr1;
             Exp2 :=Expr2;
         end;
      ir_Addr:
         with TOprExpr(Expr2) do
         begin
             Exp1 :=Expr1;
         end;
      ir_BinOp,ir_UnOp:
         begin
             with TOprExpr(Expr2) do
             begin
               Exp1 :=Expr1;
                if Expr2<> nil then  // un/bin Op
                   Exp2 :=Expr2;
             end;
         end;
    end;
    if (Exp1 <>nil)and Exp1.IsBlockVar() then
        Vars.Bits[Exp1.Address]:=ssTrue;
    if (Exp2 <>nil)and Exp2.IsBlockVar() then
        Vars.Bits[Exp2.Address]:=ssTrue;

    if (Exp3 <>nil)and Exp3.IsBlockVar() then
        Vars.Bits[Exp3.Address]:=ssTrue;
    if (Exp4 <>nil)and Exp4.IsBlockVar() then
        Vars.Bits[Exp4.Address]:=ssTrue;
end;

procedure TIRGenerator.intis_Exprs(usedvars:TBitsSet;AIR:TCompNode;ADest:TExpr);
var
 Exp1:TExpr;
 Exp2:TExpr;
 Exp3:TExpr;
 Exp4:TExpr;
begin
  Exp1 :=nil;
  Exp2 :=nil;
  Exp3 :=nil;
  Exp4 :=nil;

  with TOprExpr(AIR) do
    case xOp of
       ir_Copy:begin
           Exp1 :=Expr2;
          { if Expr2.xOp =imDeref then
             with TOprExpr(Expr2) do
             begin
                  Exp3 :=Expr1;
             end;

           if Expr1.xOp =imDeref then
             with TOprExpr(Expr1) do
             begin
                  Exp4 :=Expr1;
             end;  }
        end;
       ir_LoadParam:Exp1 :=Expr1;
       ir_Call:
         with TOprExpr(Expr1) do
         begin
             Exp1 :=Expr2;
         end;
       ir_IfFalse:Exp1 :=Expr2;
       ir_RelOp:
         with TOprExpr(Expr2) do
         begin
             Exp1 :=Expr1;
             Exp2 :=Expr2;
         end;
      ir_Addr:
        with TOprExpr(Expr2) do
         begin
             Exp1 :=Expr1;
         end;
      ir_BinOp,ir_UnOp:
         begin
             with TOprExpr(Expr2) do
             begin
               Exp1 :=Expr1;
                if Expr2<> nil then  // un/bin Op
                   Exp2 :=Expr2;
             end;
         end;
    end;

    if (Exp1 <>nil)and(Exp1.ObjLocation in [olAuto,olRet])then
       if usedvars.Bits[Exp1.Address]<>ssTrue  then
          Report_uninitialized(Exp1,AIR);
    if (Exp2 <>nil)and(Exp2.ObjLocation in [olAuto,olRet])then
       if usedvars.Bits[Exp2.Address]<>ssTrue then
          Report_uninitialized(Exp2,AIR);

    if (Exp3 <>nil)and(Exp3.ObjLocation in [olAuto,olRet])then
       if usedvars.Bits[Exp3.Address]<>ssTrue  then
          Report_uninitialized(Exp3,AIR);
    if (Exp4 <>nil)and(Exp4.ObjLocation in [olAuto,olRet])then
       if usedvars.Bits[Exp4.Address]<>ssTrue then
          Report_uninitialized(Exp4,AIR);
end;

procedure TIRGenerator.LivenessAnalyse();
var
  I,J:integer;
  IR:TCompNode;
  Expr:TExpr;
  Grph:TGraphRec;
  ExitLoop,Changed:boolean;
begin
  ExitLoop :=False;
   repeat
       Changed := False;
       for J:= 0 to FGraphsList.Count-1 do
       begin
           Grph:=FGraphsList[J];
           Grph.Vars_In_Set.changed :=false;
       end;
       for J:=0 to FGraphsList.Count-1  do
       begin
           Grph:=FGraphsList[J];

           for I :=Grph.FIRList.Count -1 downto 0 do
           begin
              IR :=Grph.FIRList[I];
              with TOprExpr(IR) do
              case xOp of
                 ir_Copy:Expr:=Expr1;
                 ir_Inc:Expr :=Expr1;
                 ir_Dec:Expr :=Expr1;
              else
                 Expr :=nil;
              end;
              if (Expr <>nil)and Expr.IsBlockVar() then
              begin
                   if ExitLoop then //last boocle
                   begin
                      if (Grph.Vars_Out_Set.Bits[Expr.Address]<>ssTrue)
                         and (Expr.ObjLocation in [olAuto,olParam,olRet])
                         and (Expr.xOp <> imOffset) then
                             Report_NotUsed_Value(Expr,IR);
                   end;
                   Grph.Vars_Out_Set.Bits[Expr.Address]:=stUndefined;
              end;
              GetUsedExprs(Grph.Vars_Out_Set,IR,Expr);
           end;

           for I := 0 to Grph.FLinks.Count-1 do
           begin
              Grph.FLinks[i].Vars_Out_Set.Union(Grph.Vars_Out_Set)
           end;
           Grph.Vars_In_Set.Copy(Grph.Vars_Out_Set);
           if Grph.Vars_In_Set.changed then
              Changed :=True;
        end;
        if ExitLoop then    // last boocle
           break;
        ExitLoop := not Changed;
    until False;
end;

procedure TIRGenerator.InitializationAnalyse();
var
   Grph,G1,G2:TGraphRec;
   Gr:TBitsSet;
   I,J:integer;
   IR:TCompNode;
   Expr:TExpr;
   U:TOprExpr;
   RetAccessible:boolean;
   ExitLoop,changed:boolean;
begin
 FGraphsList[0]._Set.Fill(ssFalse);
 ExitLoop :=False;
 Gr:=TBitsSet.Create(FActiveFunc.LocalsVarCount);
 try   RetAccessible := False;
   repeat
       Changed :=False;
       for J:= 0 to FGraphsList.Count-1 do
           FGraphsList[J]._Set.changed :=False;
       for J:= 0 to FGraphsList.Count-1 do
       begin
           Gr.Fill(ssFalse);
           Grph:=FGraphsList[J];
           if Grph.FLinks.Count>0then
              Gr.Copy(Grph.FLinks[0]._Set);
            if (Grph.FIRList.Count=1)and(Grph.FIRList[0].xOp =__TryEnd)then
             begin
               U:=TOprExpr(Grph.FIRList[0]);
               G1:= U.Expr1.Value.vPtr;
               G2:= U.Expr2.Value.vPtr;
               Gr.Union(G1._Set);
               Gr.Union(G2._Set);
             end else
                   for I :=1 to Grph.FLinks.Count -1 do
                   begin
                     Gr.InterSect(Grph.FLinks[I]._Set);
                   end;
           for I :=0 to Grph.FIRList.Count -1 do
           begin
              IR :=Grph.FIRList[I];
              Expr :=nil;
              if IR.xOp =ir_Ret then
                 RetAccessible := True;
              if IR.xOp =ir_Copy then
                 Expr :=TOprExpr(IR).Expr1;
              if ExitLoop then
                 intis_Exprs(Gr,IR,Expr);
              if (Expr <>nil)and (Expr.ObjLocation in [olAuto,olRet]) then
              begin
                 Gr.Bits[Expr.Address]:=ssTrue;
              end;
           end;
           Grph._Set.Copy(Gr);
           if Grph._Set.changed then
              Changed :=True;
        end;
        if ExitLoop then
        begin
           break;
        end;
        ExitLoop := not Changed;
    until False;
  finally
     Gr.Free;
  end;
  Grph :=FGraphsList[FGraphsList.Count-1];
  if RetAccessible then
   if not FActiveFunc.ReturnExpr.DataType.IsVoidType() then
    if Grph._Set.Bits[FActiveFunc.ReturnExpr.Address]<>ssTrue then
    begin
      FComp.Msg_Report(msNote,'Result '+FActiveFunc.Header.Name,FActiveFunc.Epilogue.Line);
    end;
end;

{ TObjsGenerator }

constructor TObjsGenerator.Create(AComp: TComp);
begin
  inherited Create(AComp);
  BinObj:=TBinObj.Create;
end;

destructor TObjsGenerator.Destroy;
begin
  BinObj.Free;
  inherited;
end;

function  TObjsGenerator.SymIndex(AExpr: TExpr):TMcLoc;
var
 cUnit:TComp;
 Idx,UnitIdx:integer;
 uf:TUnitInfo;
begin
   idx   := AExpr.Address and $FFFF;
   UnitIdx := -1;
   cUnit :=FComp;
   if AExpr.ObjLocation in [olStatic,olCode] then
   begin
       cUnit := FComp.FMainComp.GetExprUnit(AExpr);
       UnitIdx := BinObj.UnitIndex(cUnit.FUnit.Name);
       if UnitIdx =-1 then
       begin
          uf:=TUnitInfo.Create;
          UnitIdx:=BinObj.UnitsRefs.Add(uf);
          uf.Name :=cUnit.FUnit.Name;
          uf.Version := cUnit.FGenerator.BinObj.Version;
         // uf.Link :=cUnit.FGenerator.BinObj;
       end;
       case AExpr.ObjLocation of
             olCode: Result.LocType := vtCode;
           olStatic: Result.LocType := vtStatic;
       end;
       cUnit.FGenerator.BinObj.GlobalSymbs.SymbTag(idx,AExpr.DataType.TypeSize, Result.LocType);
   end else begin
       case AExpr.ObjLocation of
          olTemp,olAuto: Result.LocType := vtLocal;
          olParam,olRet: Result.LocType := vtFrame;
       else
          raise ECompException.Create('error expr location');
       end;
       cUnit.FGenerator.BinObj.Locals.SymbTag(idx,AExpr.DataType.TypeSize, Result.LocType);
   end;
   Result.Unitidx :=UnitIdx;
   Result.Addr := idx;
end;

procedure TObjsGenerator.MakeExprAddr(ARest :TByteRec;AExpr: TExpr);
var
 Expr:TOprExpr;
begin
  with ARest.CodeMc do
    case AExpr.xOp of
       imOffset:begin
             Expr :=TOprExpr(AExpr);
             if Expr.Expr1.DataType.IsTypedPointer then
             begin
               Loc.kind := vtpOffset;
               Loc.Base := SymIndex(Expr.Expr1);
             end else begin
               Loc.kind := vtOffset;
               Loc.Base := SymIndex(Expr.Expr1);
             end;
             if Expr.Expr2.ObjLocation = olLiteral then   // integer offset
             begin
                Loc.Idx.LocType := vtLiteral;
                Loc.Idx.Addr := Expr.Expr2.AsInteger;
             end else begin
                Loc.Idx  := SymIndex(Expr.Expr2);
             end;
         end;
       imDeref:begin
             Expr :=TOprExpr(AExpr);
             Loc.kind := vtPtr;
             Loc.Base := SymIndex(Expr.Expr1);
         end;
       else
            Loc.kind :=vtVar;
            Loc.Base :=SymIndex(AExpr);
    end;
end;

procedure TObjsGenerator.LoadOprnd(AExpr:TExpr;AReg:TRegDest);
var
 C:TByteRec;
begin
   C:=BinObj.NewInstruction();
   C.CodeMc.vReg :=AReg;
   if AExpr.IsConstant()and not AExpr.IsCode then
   begin
      C.CodeMc.Bytecode :=bcLiteral;
      if AExpr.DataType.TypeClass =tcFloat then
        C.CodeMc.Oprdflt := AExpr.AsNumber
      else
        C.CodeMc.OprdInt := AExpr.AsInteger;
   end else begin
     with AExpr.DataType,C.CodeMc do
     begin
        if IsIntType then
        begin
           if itSigned in BitsClass  then
           begin
              if it32Bit in BitsClass then
                 Bytecode :=bcLoad_i32
              else if it16Bit in BitsClass then
                 Bytecode := bcLoad_i16
              else if it8Bit  in BitsClass then
                 Bytecode :=bcLoad_i8
           end else begin
              if it32Bit in BitsClass then
                 Bytecode :=bcLoad_u32
              else if it16Bit in BitsClass then
                 Bytecode := bcLoad_u16
              else if it8Bit  in BitsClass then
                 Bytecode :=bcLoad_u8
           end;
        end else if IsFloatType then
        begin
           Bytecode :=bcLoad_flt
        end else begin
           case TypeSize of
                1: Bytecode :=bcLoad_u8;
                2: Bytecode :=bcLoad_u16;
                4: Bytecode :=bcLoad_u32;
                8: Bytecode :=bcLoad_64;
           end
        end;
        if C.CodeMc.Bytecode=bcNone then
            raise ECompException.Create('C.CodeMc.Bytecode=bcNone ');
        MakeExprAddr(C,AExpr);
        if IsBitsFieldType then
        begin
           C:=BinObj.NewInstruction(bcBitsRead);
           C.CodeMc.vReg :=AReg;
           with LongRec(C.CodeMc.OprdInt),TBitField(AExpr.DataType) do
           begin
               Lo := BitsOffset;
               Hi := MakeBitsMask(BitsOffset,BitsOffset+BitsCount,True); // bits mask
           end;
        end;
     end;
   end;
end;

procedure TObjsGenerator.SaveOprnd(AExpr:TExpr;AReg:TRegDest);
var
 C:TByteRec;
begin
   if AExpr.DataType.IsBitsFieldType then
   begin
       C:=BinObj.NewInstruction(bcRegToTmp);
       C.CodeMc.vReg :=AReg;
       LoadOprnd(AExpr,AReg);
       C:=BinObj.NewInstruction(bcBitsWrite);
       C.CodeMc.vReg :=AReg;
       with LongRec(C.CodeMc.OprdInt),TBitField(AExpr.DataType) do
       begin
           Lo := BitsOffset;
           Hi := MakeBitsMask(BitsOffset,BitsOffset+BitsCount,False); // bits mask
       end;
   end;
   C:=BinObj.NewInstruction();
   C.CodeMc.vReg :=AReg;
   with AExpr.DataType,C.CodeMc do
      if IsIntType then
      begin
         if itSigned in BitsClass  then
         begin
            if it32Bit in BitsClass then
               Bytecode :=bcSave_i32
            else if it16Bit in BitsClass then
               Bytecode := bcSave_i16
            else if it8Bit  in BitsClass then
               Bytecode :=bcSave_i8
         end else begin
            if it32Bit in BitsClass then
               Bytecode :=bcSave_u32
            else if it16Bit in BitsClass then
               Bytecode := bcSave_u16
            else if it8Bit  in BitsClass then
               Bytecode :=bcSave_u8
         end;
      end else if IsFloatType then
      begin
           Bytecode :=bcSave_flt
      end else begin
         case TypeSize of
              1: Bytecode :=bcSave_u8;
              2: Bytecode :=bcSave_u16;
              4: Bytecode :=bcSave_u32;
              8: Bytecode :=bcSave_64;
         end
      end;
   MakeExprAddr(C,AExpr);
end;

procedure TObjsGenerator.Loadlabel(lab:integer;AReg:TRegDest);
var
 C:TByteRec;
begin
   C:=BinObj.NewInstruction(bcLoadlabel);
   C.CodeMc.vReg :=AReg;
   C.CodeMc.OprdInt :=lab;
end;

procedure TObjsGenerator.LoadAddr(AExpr:TExpr;AReg:TRegDest);
var
 C:TByteRec;
begin
   C:=BinObj.NewInstruction(bcAddr);
   C.CodeMc.vReg :=AReg;
   MakeExprAddr(C,AExpr);
end;

procedure TObjsGenerator.LoadParam(AExpr:TExpr);
var
 C:TByteRec;
begin
   LoadOprnd(AExpr,rgReg1);
   C:=BinObj.NewInstruction(bcParam);
   C.CodeMc.vReg:=rgReg1;
   C.CodeMc.OprdInt:=AExpr.DataType.TypeSize;
end;

procedure TObjsGenerator.PushResultAddr(AExpr:TExpr);
var
 C:TByteRec;
begin
   LoadAddr(AExpr,rgReg1);
   C:=BinObj.NewInstruction(bcResultAddr);
   C.CodeMc.vReg:=rgReg1;
   C.CodeMc.OprdInt:= 4;
end;

procedure TObjsGenerator.OperationGen(AOp:TQsCmdInst;dt: TDataType);
begin
   if dt.IsFloatType then
   begin
        case AOp of
            imAdd: BinObj.NewInstruction(bcfAdd);
            imSub: BinObj.NewInstruction(bcfSub);
            imMul: BinObj.NewInstruction(bcfMul);
            imDiv: BinObj.NewInstruction(bcfDiv);
          imMinus: BinObj.NewInstruction(bcfMinus);
       end;
   end else if dt.IsIntType then
   begin
     if itSigned in dt.BitsClass then
       case AOp of
            imAdd: BinObj.NewInstruction(bciAdd);
            imSub: BinObj.NewInstruction(bciSub);
            imMul: BinObj.NewInstruction(bciMul);
            imDiv: BinObj.NewInstruction(bciDiv);
          imModul: BinObj.NewInstruction(bciModulo);
            imAnd: BinObj.NewInstruction(bcAnd);
             imOr: BinObj.NewInstruction(bcOr);
            imXor: BinObj.NewInstruction(bcXor);
            imShl: BinObj.NewInstruction(bcShl);
            imShr: BinObj.NewInstruction(bcShr);
          imMinus: BinObj.NewInstruction(bcMinus);
           imComp: BinObj.NewInstruction(bcComp);
       end else
       case AOp of
            imAdd: BinObj.NewInstruction(bcAdd);
            imSub: BinObj.NewInstruction(bcSub);
            imMul: BinObj.NewInstruction(bcMul);
            imDiv: BinObj.NewInstruction(bcDiv);
          imModul: BinObj.NewInstruction(bcModulo);
            imAnd: BinObj.NewInstruction(bcAnd);
             imOr: BinObj.NewInstruction(bcOr);
            imXor: BinObj.NewInstruction(bcXor);
            imShl: BinObj.NewInstruction(bcShl);
            imShr: BinObj.NewInstruction(bcShr);
          imMinus: BinObj.NewInstruction(bcMinus);
           imComp: BinObj.NewInstruction(bcComp);
       end
   end;
end;

procedure TObjsGenerator.Condition(AExpr:TOprExpr);
begin
   if AExpr.Expr1.DataType.IsFloatType then
   begin
       case AExpr.xOp of
         imLess: BinObj.NewInstruction(bcfLess);
           imGr: BinObj.NewInstruction(bcfGr);
      imLessEqu: BinObj.NewInstruction(bcfLessEqu);
        imGrEqu: BinObj.NewInstruction(bcfGrEqu);
          imEqu: BinObj.NewInstruction(bcfEqu);
       imNotequ: BinObj.NewInstruction(bcfNotEqu);
       end;
       Exit;
   end else if AExpr.Expr1.DataType.IsIntType then
   begin
     if itSigned in AExpr.Expr1.DataType.BitsClass then
       case AExpr.xOp of
         imLess: BinObj.NewInstruction(bciLess);
           imGr: BinObj.NewInstruction(bciGr);
      imLessEqu: BinObj.NewInstruction(bciLessEqu);
        imGrEqu: BinObj.NewInstruction(bciGrEqu);
       end else
       case AExpr.xOp of
         imLess: BinObj.NewInstruction(bcLess);
           imGr: BinObj.NewInstruction(bcGr);
      imLessEqu: BinObj.NewInstruction(bcLessEqu);
        imGrEqu: BinObj.NewInstruction(bcGrEqu);
       end
   end;
   case AExpr.xOp of
      imEqu: BinObj.NewInstruction(bcEqu);
   imNotequ: BinObj.NewInstruction(bcNotEqu);
       imIs: begin
               if AExpr.Expr2.DataType.IsPointer then // poiter to vtable
                  BinObj.NewInstruction(bc_Is_Cls)
               else                               // intger IID of the interface
                  BinObj.NewInstruction(bc_Is_Intrf);
           end
   end;
end;

procedure TObjsGenerator.Incrementation(AExpr,AFactor:TExpr;ADirection:boolean);
begin
   LoadOprnd(AExpr,rgReg1);
   LoadOprnd(AFactor,rgReg2);
   if ADirection then
      BinObj.NewInstruction(bcAdd)
   else
      BinObj.NewInstruction(bcSub);
   SaveOprnd(AExpr,rgReg3);
end;

procedure TObjsGenerator.McCopy(AExpr:TOprExpr);
begin
  LoadOprnd(AExpr.Expr2,rgReg1);
  if AExpr.Expr1.DataType.IsFloatType and AExpr.Expr2.DataType.IsIntType then
  begin
     BinObj.NewInstruction(bcInt_To_flt).CodeMc.vReg := rgReg1;
  end else if AExpr.Expr1.DataType.IsIntType and AExpr.Expr2.DataType.IsFloatType then
  begin
     BinObj.NewInstruction(bcflt_To_Int).CodeMc.vReg := rgReg1;
  end;
  SaveOprnd(AExpr.Expr1,rgReg1);
end;
var
  _LineNbr:integer;
procedure TObjsGenerator.LineNumberGen(AExpr:TOprExpr);
var
 C:TByteRec;
begin
    if AExpr.xOp = ir_Call then
       AExpr.xOp := ir_Call;
   if (AExpr.Line <>0)and(_LineNbr<>AExpr.Line) then
   begin
      _LineNbr :=AExpr.Line;
      C:=BinObj.NewInstruction(bcLineNumber);
      C.CodeMc.Loc.Base.Addr :=_LineNbr;
      C.CodeMc.Loc.Base.Unitidx:=FComp.FUnit.Address;
      if AExpr.xOp = ir_Call then // can skip
         C.CodeMc.Loc.Idx.Addr:= integer(True);
   end;
end;

procedure TObjsGenerator.ProcessGraph(AGrphs:TGraphSection;Labels:TQSList);
var
 I,J,oft,IID:integer;
 Expr,fn,N:TOprExpr;
 Grph:TGraphRec;
 Br:TByteRec;
 Dsp:TDispType;
 funcOffset:TExpr;
 vtbl:TSymIdent;
 isClassMethod:boolean;
begin
   for J :=0 to  AGrphs.Count -1 do
   begin
       Grph :=AGrphs[J];
       for i :=0 to  Grph.FIRList.Count -1 do
       begin
          Line :=BinObj.Codelength;
          Labels.Add(Pointer(Line));
          Expr :=TOprExpr(Grph.FIRList[i]);
          LineNumberGen(Expr);
          case Expr.xOp of
             ir_LoadParam: begin
                  LoadParam(Expr.Expr1);
               end;
             ir_Inc:begin
                  Incrementation(Expr.Expr1,Expr.Expr2,True);
               end;
             ir_Dec:begin
                  Incrementation(Expr.Expr1,Expr.Expr2,False);
               end;
             ir_Copy:begin
                  McCopy(Expr);
               end;
             ir_Call:begin
                  fn := TOprExpr(Expr.Expr1);
                  isClassMethod :=TFuncType(fn.Expr2.DataType).FuncKind=mkClassMethod;
                  PushResultAddr(fn.Expr1);
                  if Expr.Expr2 <> nil then // not static call
                  begin
                     oft := TFuncType(fn.Expr2.DataType).VirtualOffset;
                     funcOffset:= FComp.NewLiteralExpr(oft);
                     LoadOprnd(Expr.Expr2,rgReg1);//vTable ptr
                     LoadOprnd(funcOffset,rgReg2);
                     LoadOprnd(FComp.NewLiteralExpr(IsClassMethod),rgReg3);
                     if Expr.Expr2.DataType.IsInterface() then
                        BinObj.NewInstruction(bciCall) // call from interface
                     else
                        BinObj.NewInstruction(bcvCall); // virtual call
                  end else begin   //static call
                     LoadOprnd(fn.Expr2,rgReg1);
                     BinObj.NewInstruction(bcCall);
                  end;
               end;
             ir_Print:
                with Expr do
                 begin
                  Dsp :=ds_Unknown;
                  LoadOprnd(Expr1,rgReg1);
                  if Expr2.Value.vBool then
                  begin
                     Dsp := ds_CharArray;
                     LoadOprnd(FComp.NewLiteralExpr(TArrayType(Expr1.DataType.Dest).Count),rgReg2);
                  end else begin
                     case Expr1.DataType.TypeClass of
                       tcChar:Dsp := ds_Char;
                      tcFloat:Dsp := ds_Float;
                       tcBool:Dsp := ds_Bool;
                    tcPointer:Dsp := ds_Ptr;
                    tcInteger,
                       tcEnum:if itSigned in Expr1.DataType.BitsClass then
                                Dsp := ds_Int
                              else
                                Dsp := ds_Uint;
                         end;
                  end;
                  Br:=BinObj.NewInstruction(bcPrint);
                  Br.CodeMc.OprdInt := Ord(Dsp);
               end;
             ir_IfFalse:begin
                  LoadOprnd(Expr.Expr2,rgReg1);
                  BinObj.NewInstruction(bc_z);
                  with TOprExpr(Expr.Expr1) do
                  begin
                      Loadlabel(Expr1.AsInteger,rgReg1);
                      Loadlabel(Expr2.AsInteger,rgReg2);
                  end;
                  BinObj.NewInstruction(bcCondJump);
               end;
             ir_RelOp:begin
                   N := TOprExpr(Expr.Expr2);
                   LoadOprnd(N.Expr1,rgReg1);
                   LoadOprnd(N.Expr2,rgReg2);
                   Condition(N);
                   with TOprExpr(Expr.Expr1) do
                   begin
                      Loadlabel(Expr1.AsInteger,rgReg1);
                      Loadlabel(Expr2.AsInteger,rgReg2);
                   end;
                   BinObj.NewInstruction(bcCondJump);
               end;
             ir_Addr:
               begin
                   with TOprExpr(Expr.Expr2) do
                        LoadAddr(Expr1,rgReg1);
                   SaveOprnd(Expr.Expr1,rgReg1);
               end;
             ir_BinOp,ir_UnOp:
               begin
                  with TOprExpr(Expr.Expr2) do
                  begin
                      LoadOprnd(Expr1,rgReg1);
                      if Expr2 <> nil then  // un/bin opr
                         LoadOprnd(Expr2,rgReg2);
                      OperationGen(Expr.Expr2.xOp,Expr.Expr1.DataType);
                  end;
                  SaveOprnd(Expr.Expr1,rgReg3);
               end;
             imConstructor:
               begin
                  LoadOprnd(Expr.Expr2,rgReg1);
                  BinObj.NewInstruction(bcConstructor);
                  SaveOprnd(Expr.Expr1,rgReg1);
               end;
           ir_DynamicCast:
               begin
                  LoadOprnd(Expr.Expr2,rgReg1);
                  if Expr.Expr1.DataType.IsClass then
                  begin
                      vtbl := TClassStmt(Expr.Expr1.DataType.SymbInfo).VTable;
                      LoadOprnd(FComp.MakeAbsolutIndex(vtbl),rgReg2);
                      BinObj.NewInstruction(bcGetCls);
                  end else begin  // interface
                      IID := TInterfaceType(Expr.Expr1.DataType).IID;
                      LoadOprnd(FComp.NewLiteralExpr(IID),rgReg2);
                      BinObj.NewInstruction(bcGetIntrf);
                  end;
                  SaveOprnd(Expr.Expr1,rgReg3);
               end;
             ir_Goto:
               with TOprExpr(Expr) do
               begin
                  BinObj.NewInstruction(bcJump).CodeMc.OprdInt := Expr1.AsInteger;
               end;
            ir_TryEnter:begin
                  BinObj.NewInstruction(bcEnterHandler).CodeMc.OprdInt := Expr.Expr2.AsInteger;
               end;
            ir_ExitExcept:begin
                  BinObj.NewInstruction(bcExitHandler).CodeMc.OprdInt := 0;// no execution;
               end;
            ir_ExitFinally:begin
                  BinObj.NewInstruction(bcExitHandler).CodeMc.OprdInt := 1;// execute and remove
               end;
            ir_FinallyRet:begin
                  BinObj.NewInstruction(bcHandlerRet);
               end;
            ir_ExceptRet:begin
                  if Expr.Expr1 <> nil then
                     BinObj.NewInstruction(bcClearErr)// handle error
                  else
                     BinObj.NewInstruction(bcHandlerRet);
               end;
            ir_POPErr:begin
                  BinObj.NewInstruction(bcPopErrCode);
               end;
            ir_ErrRead:begin
                  BinObj.NewInstruction(bcReadErr);
                  SaveOprnd(Expr.Expr1,rgReg1);
               end;
            ir_Throw:begin
                  if Expr.Expr1 <> nil then
                  begin
                     LoadOprnd(Expr.Expr1,rgReg1);
                     BinObj.NewInstruction(bcRaiseError);
                  end else
                        BinObj.NewInstruction(bcReRaise);
               end;
          end;
       end;
   end;
end;

procedure TObjsGenerator.MakeObj;
var
 I,J:integer;
 Grphs:TGraphSection;
 FuncBlock:TFuncBlockStmt;
 IRLines:TQSList;
 Fe:TFuncEntry;
 Bc:TByteRec;
 ParamsSize, LocalsSize:integer;
begin
  IRLines:=TQSList.Create;
  _LineNbr:=-1;
  try
     with TTypeMembers(FComp.FUnit.DataType).Members do
      for I:=0 to Count-1 do
       with GetExpr(I), BinObj.GlobalSymbs do
        case ObjLocation of
            olCode: SymbTag(Address,0,vtCode);
          olStatic: SymbTag(Address,DataType.TypeSize,vtStatic);
        end;
     for I:=0 to FComp.FUnit.FuncList.Count-1 do
     begin
        BinObj.NewFuncEntry();
        FuncBlock := FComp.FUnit.FuncList[I];
        BinObj.Locals.EntryTag :=FuncBlock.Header.Address;
        with FuncBlock.ReturnExpr do   //ret value by reference
             BinObj.Locals.SymbTag(Address,4,vtFrame);
        for J := 0 to FuncBlock.Count -1 do   // params
         with FuncBlock.Symbols[J] do
          if ObjLocation = olParam then
             if QureyKind = atReference then
                BinObj.Locals.SymbTag(Address,4,vtFrame)
             else  {}
                BinObj.Locals.SymbTag(Address,DataType.TypeSize,vtFrame);
        Grphs :=TBlockStmt(FuncBlock.Code).Graphs;
        Bc := BinObj.NewInstruction(bcFunEnter);
        ProcessGraph(Grphs,IRLines);
        BinObj.CalcLocals(ParamsSize, LocalsSize);
        Bc.CodeMc.OprdInt := LocalsSize;
        BinObj.NewInstruction(bcRet).CodeMc.OprdInt := ParamsSize;
     end;
     // patch labels
     for I:= 0 to BinObj.FuncsList.Count -1 do
     begin
        Fe :=TFuncEntry(BinObj.FuncsList[I]);
         for J :=0 to  Fe.CodeList.Count -1 do
          with Fe.GetByteRec(J).CodeMc do
           if Bytecode in [bcJump,bcloadLabel,bcEnterHandler]then
              OprdInt := integer(IRLines[OprdInt]);
      end;
  finally
    _LineNbr:=-1;
    IRLines.Free;
  end;
end;

end.
