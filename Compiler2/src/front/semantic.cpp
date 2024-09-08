#include"front/semantic.h"

#include<cassert>
#include <utility>

using ir::Instruction;
using ir::Function;
using ir::Operand;
using ir::Operator;

#define TODO assert(0 && "TODO");

#define GET_CHILD_PTR(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); 
#define ANALYSIS(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); analysis##type(node, buffer);
#define COPY_EXP_NODE(from, to) to->is_computable = from->is_computable; to->v = from->v; to->t = from->t;

map<std::string,ir::Function*>* frontend::get_lib_funcs() {
    static map<std::string,ir::Function*> lib_funcs = {
        {"getint", new Function("getint", Type::Int)},
        {"getch", new Function("getch", Type::Int)},
        {"getfloat", new Function("getfloat", Type::Float)},
        {"getarray", new Function("getarray", {Operand("arr", Type::IntPtr)}, Type::Int)},
        {"getfarray", new Function("getfarray", {Operand("arr", Type::FloatPtr)}, Type::Int)},
        {"putint", new Function("putint", {Operand("i", Type::Int)}, Type::null)},
        {"putch", new Function("putch", {Operand("i", Type::Int)}, Type::null)},
        {"putfloat", new Function("putfloat", {Operand("f", Type::Float)}, Type::null)},
        {"putarray", new Function("putarray", {Operand("n", Type::Int), Operand("arr", Type::IntPtr)}, Type::null)},
        {"putfarray", new Function("putfarray", {Operand("n", Type::Int), Operand("arr", Type::FloatPtr)}, Type::null)},
    };
    return &lib_funcs;
}

void frontend::SymbolTable::add_scope(string type) {
    frontend::ScopeInfo scopeInfo;
    scopeInfo.name=std::move(type);
    if (scope_stack.empty()){
        scopeInfo.cnt=1;
    }
    else{
        scopeInfo.cnt=scope_stack.back().cnt+1;
    }
    scope_stack.push_back(scopeInfo);
}
void frontend::SymbolTable::exit_scope() {
    scope_stack.pop_back();
}

string frontend::SymbolTable::get_scoped_name(const string& id) const {
    //获得变量在当前作用域下的名称
    return id+"_"+scope_stack.back().name+ std::to_string(scope_stack.back().cnt);
}

Operand frontend::SymbolTable::get_operand(const string& id) {
    for (int i=int(scope_stack.size())-1;i>=0;i--){
        if (scope_stack[i].table.count(id)){
            return scope_stack[i].table[id].operand;
        }
    }
    assert(0 && "Error in get_operand!");
    return {};
}

frontend::STE frontend::SymbolTable::get_ste(const string& id) {
    for (int i=int(scope_stack.size())-1;i>=0;i--){
        if (scope_stack[i].table.count(id)){
            return scope_stack[i].table[id];
        }
    }
    assert(0 && "Error in get_ste!");
    return {};
}

frontend::Analyzer::Analyzer(): tmp_cnt(0), symbol_table() {

}

ir::Program frontend::Analyzer::get_ir_program(CompUnit* root) {
    //添加全局作用域
    symbol_table.add_scope("global");
    //添加全局函数
    auto global_func=new ir::Function("global",ir::Type::null);
    symbol_table.functions["global"]=global_func;
    //symbol_table.functions["__cur__"]=global_func;
    //添加库函数
    auto lib_funcs=*get_lib_funcs();
    for (auto & lib_func : lib_funcs){
        symbol_table.functions[lib_func.first]=lib_func.second;
    }
    ir::Program program;
    //开始分析
    analysisCompUnit(root,program);
    //添加全局作用域的变量
    for (auto& global_value:symbol_table.scope_stack[0].table){
        //变量可能为数组
        if (!global_value.second.dimension.empty()){
            int len=1;
            for (int i:global_value.second.dimension){
                len*=i;
            }
            program.globalVal.push_back({{global_value.second.operand.name,global_value.second.operand.type},len});
        }
        //字面值不添加，只添加变量
        else if (global_value.second.operand.type!=Type::IntLiteral&&global_value.second.operand.type!=Type::FloatLiteral){
            program.globalVal.push_back({{global_value.second.operand.name,global_value.second.operand.type}});
        }
    }
    //全局函数返回
    global_func->addInst(new ir::Instruction(ir::Operand(),ir::Operand(),ir::Operand(),ir::Operator::_return));
    program.addFunction(*global_func);
    return program;
}

void frontend::Analyzer::analysisCompUnit(frontend::CompUnit* root,ir::Program& buffer){
    //CompUnit -> (Decl | FuncDef) [CompUnit]

    if (auto* decl=dynamic_cast<Decl*>(root->children[0])){
        vector<ir::Instruction*> instructions;
        analysisDecl(decl,instructions);
        for (auto& inst:instructions){
            symbol_table.functions["global"]->addInst(inst);
        }
    }
    else if (auto* funcDef=dynamic_cast<FuncDef*>(root->children[0])){
        ir::Function func;
        analysisFuncDef(funcDef,func);
        buffer.addFunction(func);
    }
    else{
        assert(0 && "Error in compunit!");
    }
    if (int(root->children.size())==2){
        auto* compUnit=dynamic_cast<CompUnit*>(root->children[1]);
        analysisCompUnit(compUnit,buffer);
    }
}

void frontend::Analyzer::analysisFuncDef(frontend::FuncDef* root,ir::Function& buffer){
    //FuncDef -> FuncType Ident '(' [FuncFParams] ')' Block
    //FuncDef.t
    //FuncDef.n

    //确定返回值类型
    ir::Type funcReturnType;
    analysisFuncType(dynamic_cast<FuncType*>(root->children[0]),funcReturnType);
    //确定函数名
    string funcName=dynamic_cast<Term*>(root->children[1])->token.value;
    //进入函数作用域
    symbol_table.add_scope("function");
    //判断是否有参数
    vector<ir::Operand> params;
    if (auto* funcFParams=dynamic_cast<FuncFParams*>(root->children[3])){
        analysisFuncFParams(funcFParams,params);
    }
    //创建函数
    buffer.name=funcName;
    buffer.ParameterList=params;
    buffer.returnType=funcReturnType;
    //main函数增加全局函数调用
    if (funcName=="main"){
        buffer.addInst(new ir::CallInst(ir::Operand("global", ir::Type::null),
                                        ir::Operand("t"+std::to_string(tmp_cnt++), ir::Type::null)));
    }
    symbol_table.functions[funcName]=&buffer;
    //记录现在所处的函数
    symbol_table.functions["__cur__"]=&buffer;
    //分析函数体
    vector<ir::Instruction*> funcInstructions;
    analysisBlock(dynamic_cast<Block*>(root->children.back()),funcInstructions);
    symbol_table.exit_scope();
    //填充指令
    for (auto inst:funcInstructions){
        buffer.addInst(inst);
    }
    //main函数新增return 0,void函数新增return null
    if (funcName=="main"){
        buffer.addInst(new ir::Instruction(ir::Operand("0",ir::Type::IntLiteral),
                                           ir::Operand(),
                                           ir::Operand(),
                                           ir::Operator::_return));
    }
    if (funcReturnType==Type::null){
        buffer.addInst(new ir::Instruction(ir::Operand(),
                                           ir::Operand(),
                                           ir::Operand(),
                                           ir::Operator::_return));
    }
}

void frontend::Analyzer::analysisDecl(frontend::Decl* root,vector<ir::Instruction*>& buffer){
    //Decl -> ConstDecl | VarDecl

    if (auto* constDecl=dynamic_cast<ConstDecl*>(root->children[0])){
        analysisConstDecl(constDecl,buffer);
    }
    else if (auto* varDecl=dynamic_cast<VarDecl*>(root->children[0])){
        analysisVarDecl(varDecl,buffer);
    }
    else{
        assert(0 && "Error in decl!");
    }
}

void frontend::Analyzer::analysisConstDecl(frontend::ConstDecl* root,vector<ir::Instruction*>& buffer){
    //ConstDecl -> 'const' BType ConstDef { ',' ConstDef } ';'
    //ConstDecl.t

    //解析BType
    ir::Type type;
    analysisBType(dynamic_cast<BType*>(root->children[1]),type);
    //解析ConstDef
    for (int i=2;i<int(root->children.size());i+=2){
        analysisConstDef(dynamic_cast<ConstDef*>(root->children[i]),buffer,type);
    }
}

void frontend::Analyzer::analysisBType(frontend::BType* root,ir::Type& buffer){
    //BType -> 'int' | 'float'
    //BType.t

    Term* term=dynamic_cast<Term*>(root->children[0]);
    if (term->token.type==TokenType::INTTK){
        buffer=ir::Type::Int;
    }
    else if (term->token.type==TokenType::FLOATTK){
        buffer=ir::Type::Float;
    }
    else{
        assert(0 && "Error in btype!");
    }
}

void frontend::Analyzer::analysisConstDef(frontend::ConstDef* root,vector<ir::Instruction*>& buffer,Type& type){
    //ConstDef -> Ident { '[' ConstExp ']' } '=' ConstInitVal
    //ConstDef.arr_name

    //确定变量名
    string varName=dynamic_cast<Term*>(root->children[0])->token.value;
    //注意：在本实验中变量包括普通变量、一维数组、二维数组
    //普通变量
    if (int(root->children.size())==3){
        //插入符号表
        STE ste;
        if (type==Type::Int){
            ste.operand=Operand(symbol_table.get_scoped_name(varName),Type::IntLiteral);
        }
        else{  //Float
            ste.operand=Operand(symbol_table.get_scoped_name(varName),Type::FloatLiteral);
        }
        auto* constInitVal=dynamic_cast<ConstInitVal*>(root->children[2]);
        vector<ir::Operand> temp;
        analysisConstInitVal(constInitVal,buffer,temp);
        //需要存放计算出的值
        ste.literalValue=constInitVal->v;
        symbol_table.scope_stack.back().table[varName]=ste;
    }
    //一维数组
    else if (int(root->children.size())==6){
        auto* constExp=dynamic_cast<ConstExp*>(root->children[2]);
        analysisConstExp(constExp,buffer);
        assert(constExp->t==Type::IntLiteral||constExp->t==Type::FloatLiteral);
        int arrLen= std::stoi(constExp->v);
        STE ste;
        ste.dimension={arrLen};
        Type arrPtrType;
        if (type==Type::Int){
            arrPtrType=Type::IntPtr;
        }
        else{
            arrPtrType=Type::FloatPtr;
        }
        ste.operand=ir::Operand(symbol_table.get_scoped_name(varName),arrPtrType);
        symbol_table.scope_stack.back().table[varName]=ste;
        //为数组分配内存
        if (int(symbol_table.scope_stack.size())>1){
            buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(arrLen),Type::IntLiteral),
                                                 ir::Operand(),
                                                 ir::Operand(ste.operand.name,arrPtrType),
                                                 ir::Operator::alloc));
        }
        //初始化
        auto* constInitVal=dynamic_cast<ConstInitVal*>(root->children[5]);
        vector<ir::Operand> values;
        analysisConstInitVal(constInitVal,buffer,values);
        int index=0;
        for (;index<int(values.size());index++){
            if (arrPtrType==Type::IntPtr){
                buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                     ir::Operand(std::to_string(index),Type::IntLiteral),
                                                     ir::Operand(std::to_string(std::stoi(values[index].name)),Type::IntLiteral),
                                                                 ir::Operator::store));
            }
            else{  //FloatPtr
                buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                     ir::Operand(std::to_string(index),Type::IntLiteral),
                                                     ir::Operand(std::to_string(std::stof(values[index].name)),Type::FloatLiteral),
                                                     ir::Operator::store));
            }
        }
        //局部变量默认初始化为0
        if (int(symbol_table.scope_stack.size())>1){
            for (;index<arrLen;index++){
                if (arrPtrType==Type::IntPtr){
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ir::Type::IntPtr),
                                                         ir::Operand(std::to_string(index),Type::IntLiteral),
                                                         ir::Operand("0",Type::IntLiteral),
                                                         ir::Operator::store));
                }
                else{
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ir::Type::FloatPtr),
                                                         ir::Operand(std::to_string(index),Type::IntLiteral),
                                                         ir::Operand("0.0",Type::FloatLiteral),
                                                         ir::Operator::store));
                }
            }
        }
    }
    //二维数组
    else if (int(root->children.size())==9){
        auto* constExp1=dynamic_cast<ConstExp*>(root->children[2]);
        auto* constExp2=dynamic_cast<ConstExp*>(root->children[5]);
        //计算维度
        analysisConstExp(constExp1,buffer);
        assert(constExp1->t==Type::IntLiteral||constExp1->t==Type::FloatLiteral);
        analysisConstExp(constExp2,buffer);
        assert(constExp2->t==Type::IntLiteral||constExp2->t==Type::FloatLiteral);
        int dim1= std::stoi(constExp1->v);
        int dim2= std::stoi(constExp2->v);
        int arrLen=dim1*dim2;
        STE ste;
        ste.dimension={dim1,dim2};
        Type arrPtrType;
        if (type==Type::Int){
            arrPtrType=Type::IntPtr;
        }
        else{
            arrPtrType=Type::FloatPtr;
        }
        ste.operand=ir::Operand(symbol_table.get_scoped_name(varName),arrPtrType);
        symbol_table.scope_stack.back().table[varName]=ste;
        //为数组分配内存
        if (int(symbol_table.scope_stack.size())>1){
            buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(arrLen),Type::IntLiteral),
                                                 ir::Operand(),
                                                 ir::Operand(ste.operand.name,arrPtrType),
                                                 ir::Operator::alloc));
        }
        //初始化
        auto* constInitVal=dynamic_cast<ConstInitVal*>(root->children[5]);
        vector<ir::Operand> values;
        analysisConstInitVal(constInitVal,buffer,values);
        int index=0;
        for (;index<int(values.size());index++){
            if (arrPtrType==Type::IntPtr){
                buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                     ir::Operand(std::to_string(index),Type::IntLiteral),
                                                     ir::Operand(std::to_string(std::stoi(values[index].name)),Type::IntLiteral),
                                                     ir::Operator::store));
            }
            else{  //FloatPtr
                buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                     ir::Operand(std::to_string(index),Type::IntLiteral),
                                                     ir::Operand(std::to_string(std::stof(values[index].name)),Type::FloatLiteral),
                                                     ir::Operator::store));
            }
        }
        //局部变量默认初始化为0
        if (int(symbol_table.scope_stack.size())>1){
            for (;index<arrLen;index++){
                if (arrPtrType==Type::IntPtr){
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ir::Type::IntPtr),
                                                         ir::Operand(std::to_string(index),Type::IntLiteral),
                                                         ir::Operand("0",Type::IntLiteral),
                                                         ir::Operator::store));
                }
                else{
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ir::Type::FloatPtr),
                                                         ir::Operand(std::to_string(index),Type::IntLiteral),
                                                         ir::Operand("0.0",Type::FloatLiteral),
                                                         ir::Operator::store));
                }
            }
        }
    }
    else{
        assert(0 && "Error in constdef!");
    }
}

void frontend::Analyzer::analysisConstInitVal(frontend::ConstInitVal* root,vector<ir::Instruction*>& buffer,vector<ir::Operand>& values){
    //ConstInitVal -> ConstExp | '{' [ ConstInitVal { ',' ConstInitVal } ] '}'
    //ConstInitVal.v
    //ConstInitVal.t

    //如果为ConstExp则设置节点值，否则将每个子节点值存在values中

    if (int(root->children.size())==1){
        auto constExp=dynamic_cast<ConstExp*>(root->children[0]);
        analysisConstExp(constExp,buffer);
        assert(constExp->t==Type::IntLiteral||constExp->t==Type::FloatLiteral);
        root->t=constExp->t;
        root->v=constExp->v;
    }
    else if (int(root->children.size())>2){
        for (int i=1;i<int(root->children.size());i+=2){
            auto son=dynamic_cast<ConstInitVal*>(root->children[i]);
            //认为是ConstExp
            vector<ir::Operand> temp;
            analysisConstInitVal(son,buffer,temp);
            assert(son->t==Type::IntLiteral||son->t==Type::FloatLiteral);
            values.emplace_back(ir::Operand(son->v,son->t));
        }
    }
    else{
        ;
    }
}

void frontend::Analyzer::analysisVarDecl(frontend::VarDecl* root,vector<ir::Instruction*>& buffer){
    //VarDecl -> BType VarDef { ',' VarDef } ';'
    //VarDecl.t

    //解析BType;
    ir::Type type;
    analysisBType(dynamic_cast<BType*>(root->children[0]),type);
    //解析VarDef
    for (int i=1;i<int(root->children.size());i+=2){
        analysisVarDef(dynamic_cast<VarDef*>(root->children[i]),buffer,type);
    }
}

void frontend::Analyzer::analysisVarDef(frontend::VarDef* root,vector<ir::Instruction*>& buffer,Type& type){
    //VarDef -> Ident { '[' ConstExp ']' } [ '=' InitVal ]
    //VarDef.arr_name

    auto* term=dynamic_cast<Term*>(root->children[0]);
    //变量名
    string varName=term->token.value;
    //普通变量
    if (int(root->children.size())<4){
        STE ste;
        ste.operand=ir::Operand(symbol_table.get_scoped_name(varName),type);
        symbol_table.scope_stack.back().table[varName]=ste;
        //默认初始化
        if (int(root->children.size())==1){
            if (type==Type::Int){
                buffer.push_back(new ir::Instruction(ir::Operand("0",Type::IntLiteral),
                                                     ir::Operand(),
                                                     ir::Operand(ste.operand.name,Type::Int),
                                                     ir::Operator::def));
            }
            else{ //Float
                buffer.push_back(new ir::Instruction(ir::Operand("0.0",Type::FloatLiteral),
                                                     ir::Operand(),
                                                     ir::Operand(ste.operand.name,Type::Float),
                                                     ir::Operator::fdef));
            }
        }
        //初始化
        else{
            auto* initVal=dynamic_cast<InitVal*>(root->children[2]);
            vector<ir::Operand> temp;
            analysisInitVal(initVal,buffer,temp);
            if (type==Type::Int){
                if (initVal->t==Type::Int||initVal->t==Type::IntLiteral){
                    buffer.push_back(new ir::Instruction(ir::Operand(initVal->v,initVal->t),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Int),
                                                         ir::Operator::def));
                }
                else if (initVal->t==Type::Float){
                    string tempVar="t"+ std::to_string(tmp_cnt++);
                    buffer.push_back(new ir::Instruction(ir::Operand(initVal->v,Type::Float),
                                                         ir::Operand(),
                                                         ir::Operand(tempVar,Type::Int),
                                                         ir::Operator::cvt_f2i));
                    buffer.push_back(new ir::Instruction(ir::Operand(tempVar,Type::Int),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Int),
                                                         ir::Operator::def));
                }
                else if (initVal->t==Type::FloatLiteral){
                    buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(std::stoi(initVal->v)),Type::IntLiteral),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Int),
                                                         ir::Operator::def));
                }
                else{
                    assert(0 && "Error in vardef!");
                }
            }
            else{  //Float
                if (initVal->t==Type::IntLiteral||initVal->t==Type::FloatLiteral){
                    buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(std::stof(initVal->v)),Type::FloatLiteral),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Float),
                                                         ir::Operator::fdef));
                }
                else if (initVal->t==Type::Int){
                    string tempVar="t"+ std::to_string(tmp_cnt++);
                    buffer.push_back(new ir::Instruction(ir::Operand(initVal->v,Type::Int),
                                                         ir::Operand(),
                                                         ir::Operand(tempVar,Type::Float),
                                                         ir::Operator::cvt_i2f));
                    buffer.push_back(new ir::Instruction(ir::Operand(tempVar,Type::Float),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Float),
                                                         ir::Operator::fdef));
                }
                else if (initVal->t==Type::Float){
                    buffer.push_back(new ir::Instruction(ir::Operand(initVal->v,Type::Float),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Float),
                                                         ir::Operator::fdef));
                }
                else{
                    assert(0 && "Error in vardef!");
                }
            }
        }
    }
    //一维数组
    else if (int(root->children.size())<7){
        auto* constExp=dynamic_cast<ConstExp*>(root->children[2]);
        analysisConstExp(constExp,buffer);
        assert(constExp->t==Type::IntLiteral||constExp->t==Type::FloatLiteral);
        int arrLen= std::stoi(constExp->v);
        STE ste;
        ste.dimension={arrLen};
        Type arrPtrType;
        if (type==Type::Int){
            arrPtrType=Type::IntPtr;
        }
        else{
            arrPtrType=Type::FloatPtr;
        }
        ste.operand=ir::Operand(symbol_table.get_scoped_name(varName),arrPtrType);
        symbol_table.scope_stack.back().table[varName]=ste;
        //为数组分配内存
        if (int(symbol_table.scope_stack.size())>1){
            buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(arrLen),Type::IntLiteral),
                                                 ir::Operand(),
                                                 ir::Operand(ste.operand.name,arrPtrType),
                                                 ir::Operator::alloc));
        }
        //数组初始化
        if (auto* initVal=dynamic_cast<InitVal*>(root->children.back())){
            vector<ir::Operand> values;
            analysisInitVal(initVal,buffer,values);
            int index=0;
            for (;index<int(values.size());index++){
                if (arrPtrType==Type::IntPtr){
                    if (values[index].type==Type::Int||values[index].type==Type::IntLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(values[index].name,values[index].type),
                                                             ir::Operator::store));
                    }
                    else if (values[index].type==Type::FloatLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(std::to_string(std::stoi(values[index].name)),Type::IntLiteral),
                                                             ir::Operator::store));
                    }
                    else if (values[index].type==Type::Float){
                        string tempVar="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(values[index].name,Type::Float),
                                                             ir::Operand(),
                                                             ir::Operand(tempVar,Type::Int),
                                                             ir::Operator::cvt_f2i));
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(tempVar,Type::Int),
                                                             ir::Operator::store));
                    }
                    else{
                        assert(0 && "Error in vardef!");
                    }
                }
                else{  //FloatPtr
                    if (values[index].type==Type::IntLiteral||values[index].type==Type::FloatLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(std::to_string(std::stof(values[index].name)),Type::FloatLiteral),
                                                             ir::Operator::store));
                    }
                    else if (values[index].type==Type::Int){
                        string tempVar="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(values[index].name,Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempVar,Type::Float),
                                                             ir::Operator::cvt_i2f));
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(tempVar,Type::Float),
                                                             ir::Operator::store));
                    }
                    else if (values[index].type==Type::Float){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(values[index].name,Type::Float),
                                                             ir::Operator::store));
                    }
                    else{
                        assert(0 && "Error in vardef!");
                    }
                }
            }
            //局部变量默认初始化为0
            if (int(symbol_table.scope_stack.size())>1){
                for (;index<arrLen;index++){
                    if (arrPtrType==Type::IntPtr){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ir::Type::IntPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand("0",Type::IntLiteral),
                                                             ir::Operator::store));
                    }
                    else{
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ir::Type::FloatPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand("0.0",Type::FloatLiteral),
                                                             ir::Operator::store));
                    }
                }
            }
        }
    }
    //二维数组
    else{
        auto* constExp1=dynamic_cast<ConstExp*>(root->children[2]);
        auto* constExp2=dynamic_cast<ConstExp*>(root->children[5]);
        //计算维度
        analysisConstExp(constExp1,buffer);
        assert(constExp1->t==Type::IntLiteral||constExp1->t==Type::FloatLiteral);
        analysisConstExp(constExp2,buffer);
        assert(constExp2->t==Type::IntLiteral||constExp2->t==Type::FloatLiteral);
        int dim1= std::stoi(constExp1->v);
        int dim2= std::stoi(constExp2->v);
        int arrLen=dim1*dim2;
        STE ste;
        ste.dimension={dim1,dim2};
        Type arrPtrType;
        if (type==Type::Int){
            arrPtrType=Type::IntPtr;
        }
        else{
            arrPtrType=Type::FloatPtr;
        }
        ste.operand=ir::Operand(symbol_table.get_scoped_name(varName),arrPtrType);
        symbol_table.scope_stack.back().table[varName]=ste;
        //为数组分配内存
        if (int(symbol_table.scope_stack.size())>1){
            buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(arrLen),Type::IntLiteral),
                                                 ir::Operand(),
                                                 ir::Operand(ste.operand.name,arrPtrType),
                                                 ir::Operator::alloc));
        }
        //判断是否初始化
        if (auto* initVal=dynamic_cast<InitVal*>(root->children.back())){
            vector<ir::Operand> values;
            analysisInitVal(initVal,buffer,values);
            int index=0;
            for (;index<int(values.size());index++){
                if (arrPtrType==Type::IntPtr){
                    if (values[index].type==Type::Int||values[index].type==Type::IntLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(values[index].name,values[index].type),
                                                             ir::Operator::store));
                    }
                    else if (values[index].type==Type::FloatLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(std::to_string(std::stoi(values[index].name)),Type::IntLiteral),
                                                             ir::Operator::store));
                    }
                    else if (values[index].type==Type::Float){
                        string tempVar="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(values[index].name,Type::Float),
                                                             ir::Operand(),
                                                             ir::Operand(tempVar,Type::Int),
                                                             ir::Operator::cvt_f2i));
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(tempVar,Type::Int),
                                                             ir::Operator::store));
                    }
                    else{
                        assert(0 && "Error in vardef!");
                    }
                }
                else{  //FloatPtr
                    if (values[index].type==Type::IntLiteral||values[index].type==Type::FloatLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(std::to_string(std::stof(values[index].name)),Type::FloatLiteral),
                                                             ir::Operator::store));
                    }
                    else if (values[index].type==Type::Int){
                        string tempVar="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(values[index].name,Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempVar,Type::Float),
                                                             ir::Operator::cvt_i2f));
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(tempVar,Type::Float),
                                                             ir::Operator::store));
                    }
                    else if (values[index].type==Type::Float){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand(values[index].name,Type::Float),
                                                             ir::Operator::store));
                    }
                    else{
                        assert(0 && "Error in vardef!");
                    }
                }
            }
            //局部变量默认初始化为0
            if (int(symbol_table.scope_stack.size())>1){
                for (;index<arrLen;index++){
                    if (arrPtrType==Type::IntPtr){
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ir::Type::IntPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand("0",Type::IntLiteral),
                                                             ir::Operator::store));
                    }
                    else{
                        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ir::Type::FloatPtr),
                                                             ir::Operand(std::to_string(index),Type::IntLiteral),
                                                             ir::Operand("0.0",Type::FloatLiteral),
                                                             ir::Operator::store));
                    }
                }
            }
        }
    }
}

void frontend::Analyzer::analysisInitVal(frontend::InitVal* root,vector<ir::Instruction*>& buffer,vector<ir::Operand>& values){
    //InitVal -> Exp | '{' [ InitVal { ',' InitVal } ] '}'
    //InitVal.is_computable
    //InitVal.v
    //InitVal.t

    //如果为Exp节点则将值存储在节点中，否则存在values中

    if (int(root->children.size())==1){
        auto exp=dynamic_cast<Exp*>(root->children[0]);
        analysisExp(exp,buffer);
        root->t=exp->t;
        root->v=exp->v;
    }
    else if (int(root->children.size())>2){
        for (int i=1;i<int(root->children.size());i+=2){
            auto son=dynamic_cast<InitVal*>(root->children[i]);
            //认为是Exp
            vector<ir::Operand> temp;
            analysisInitVal(son,buffer,temp);
            values.emplace_back(ir::Operand(son->v,son->t));
        }
    }
    else{
        ;
    }
}

void frontend::Analyzer::analysisFuncType(frontend::FuncType* root,ir::Type& buffer){
    //FuncType -> 'void' | 'int' | 'float'

    Term* term=dynamic_cast<Term*>(root->children[0]);
    if (term->token.type==TokenType::VOIDTK){
        buffer=ir::Type::null;
    }
    else if (term->token.type==TokenType::INTTK){
        buffer=ir::Type::Int;
    }
    else if (term->token.type==TokenType::FLOATTK){
        buffer=ir::Type::Float;
    }
    else{
        assert(0 && "Error in functype!");
    }
}

void frontend::Analyzer::analysisFuncFParam(frontend::FuncFParam* root,ir::Operand& buffer){
    //FuncFParam -> BType Ident ['[' ']' { '[' Exp ']' }]

    ir::Type paramType;
    analysisBType(dynamic_cast<BType*>(root->children[0]),paramType);
    string paramName=dynamic_cast<Term*>(root->children[1])->token.value;
    //判断是否为数组 注意：用例中最多出现二维数组
    //如果为数组则变量名为指针
    vector<int> dimension={};
    if (int(root->children.size())>2){
        dimension.push_back(-1);
        if (paramType==Type::Int){
            paramType=Type::IntPtr;
        }
        else if (paramType==Type::Float){
            paramType=Type::FloatPtr;
        }
        else{
            assert(0 && "Error in funcfparam!");
        }
        if (int(root->children.size())==7){
            vector<ir::Instruction*> instructions;
            analysisExp(dynamic_cast<Exp*>(root->children[5]),instructions);
            int res= std::stoi(dynamic_cast<Exp*>(root->children[5])->v);
            dimension.push_back(res);
        }
    }
    buffer.name=symbol_table.get_scoped_name(paramName);
    buffer.type=paramType;
    STE ste;
    ste.operand=buffer;
    ste.dimension=dimension;
    //加入作用域
    symbol_table.scope_stack.back().table[paramName]=ste;
}

void frontend::Analyzer::analysisFuncFParams(frontend::FuncFParams* root,vector<ir::Operand>& buffer){
    //FuncFParams -> FuncFParam { ',' FuncFParam }
    for (int i=0;i<int(root->children.size());i+=2){
        ir::Operand operand;
        analysisFuncFParam(dynamic_cast<FuncFParam*>(root->children[i]),operand);
        buffer.emplace_back(operand);
    }
}

void frontend::Analyzer::analysisBlock(frontend::Block* root,vector<ir::Instruction*>& buffer){
    //Block -> '{' { BlockItem } '}'

    //注意 分析Block时请先创建作用域
    for (int i=1;i<int(root->children.size())-1;i++){
        analysisBlockItem(dynamic_cast<BlockItem*>(root->children[i]),buffer);
    }
}

void frontend::Analyzer::analysisBlockItem(frontend::BlockItem* root,vector<ir::Instruction*>& buffer){
    //BlockItem -> Decl | Stmt

    if (Decl* decl=dynamic_cast<Decl*>(root->children[0])){
        analysisDecl(decl,buffer);
    }
    else if (Stmt* stmt=dynamic_cast<Stmt*>(root->children[0])){
        analysisStmt(stmt,buffer);
    }
    else{
        assert(0 && "Error in blockitem!");
    }
}

void frontend::Analyzer::analysisStmt(frontend::Stmt* root,vector<ir::Instruction*>& buffer){
    //Stmt -> LVal '=' Exp ';' | Block | 'if' '(' Cond ')' Stmt [ 'else' Stmt ]
    // | 'while' '(' Cond ')' Stmt | 'break' ';' | 'continue' ';' | 'return' [Exp] ';' | [Exp] ';'

    //LVal
    if (auto* lVal=dynamic_cast<LVal*>(root->children[0])){
        string varName;
        ir::Operand offset;
        analysisLVal(lVal,buffer,varName,offset);
        auto* exp=dynamic_cast<Exp*>(root->children[2]);
        analysisExp(exp,buffer);
        STE ste=symbol_table.get_ste(varName);
        //普通变量赋值
        if (offset.name=="-1"&&offset.type==Type::IntLiteral){
            if (ste.operand.type==Type::Int){
                if (exp->t==Type::Int){
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::Int),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Int),
                                                         ir::Operator::mov));
                }
                else if (exp->t==Type::IntLiteral){
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::IntLiteral),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Int),
                                                         ir::Operator::mov));
                }
                else if (exp->t==Type::Float){
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::Float),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Int),
                                                         ir::Operator::cvt_f2i));
                }
                else{  //FloatLiteral
                    buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(std::stoi(exp->v)),Type::IntLiteral),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Int),
                                                         ir::Operator::mov));
                }
            }
            else if (ste.operand.type==Type::Float){
                if (exp->t==Type::Int){
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::Int),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Float),
                                                         ir::Operator::cvt_i2f));
                }
                else if (exp->t==Type::IntLiteral){
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::FloatLiteral),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Float),
                                                         ir::Operator::fmov));
                }
                else if (exp->t==Type::Float){
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::Float),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Float),
                                                         ir::Operator::fmov));
                }
                else{  //FloatLiteral
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::FloatLiteral),
                                                         ir::Operand(),
                                                         ir::Operand(ste.operand.name,Type::Float),
                                                         ir::Operator::fmov));
                }
            }
            else{
                assert(0 && "Error in stmt!");
            }
        }
        //数组赋值
        else{
            if (ste.operand.type==Type::IntPtr){
                if (exp->t==Type::Int||exp->t==Type::IntLiteral){
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                         ir::Operand(offset.name,offset.type),
                                                         ir::Operand(exp->v,exp->t),
                                                         ir::Operator::store));
                }
                else if (exp->t==Type::Float){
                    string tempVar="t"+ std::to_string(tmp_cnt++);
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::Float),
                                                         ir::Operand(),
                                                         ir::Operand(tempVar,Type::Int),
                                                         ir::Operator::cvt_f2i));
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                         ir::Operand(offset.name,offset.type),
                                                         ir::Operand(tempVar,Type::Int),
                                                         ir::Operator::store));
                }
                else{  //FloatLiteral
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::IntPtr),
                                                         ir::Operand(offset.name,offset.type),
                                                         ir::Operand(std::to_string(std::stoi(exp->v)),Type::IntLiteral),
                                                         ir::Operator::store));
                }
            }
            else{  //FloatPtr
                if (exp->t==Type::Float||exp->t==Type::FloatLiteral){
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                         ir::Operand(offset.name,offset.type),
                                                         ir::Operand(exp->v,exp->t),
                                                         ir::Operator::store));
                }
                else if (exp->t==Type::Int){
                    string tempVar="t"+ std::to_string(tmp_cnt++);
                    buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::Int),
                                                         ir::Operand(),
                                                         ir::Operand(tempVar,Type::Float),
                                                         ir::Operator::cvt_i2f));
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                         ir::Operand(offset.name,offset.type),
                                                         ir::Operand(tempVar,Type::Float),
                                                         ir::Operator::store));
                }
                else{  //IntLiteral
                    buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,Type::FloatPtr),
                                                         ir::Operand(offset.name,offset.type),
                                                         ir::Operand(std::to_string(std::stof(exp->v)),Type::FloatLiteral),
                                                         ir::Operator::store));
                }
            }
        }
    }
    //Block分支
    else if (auto* block=dynamic_cast<Block*>(root->children[0])){
        //新建作用域
        symbol_table.add_scope("block");
        analysisBlock(block,buffer);
        symbol_table.exit_scope();
    }
    //exp ;
    else if (auto* exp=dynamic_cast<Exp*>(root->children[0])){
        analysisExp(exp,buffer);
    }
    //if while break continue return ;
    else{
        auto* term=dynamic_cast<Term*>(root->children[0]);
        //if
        if (term->token.type==TokenType::IFTK){
            auto* cond=dynamic_cast<Cond*>(root->children[2]);
            analysisCond(cond,buffer);
            //cond的值转为整数
            if (cond->t==Type::FloatLiteral){
                cond->v= std::to_string(std::stof(cond->v)!=0);
                cond->t=Type::IntLiteral;
            }
            if (cond->t==Type::Float){
                string tempRes1="t"+ std::to_string(tmp_cnt++);
                buffer.push_back(new ir::Instruction(ir::Operand(cond->v,Type::Float),
                                                     ir::Operand("0.0",Type::FloatLiteral),
                                                     ir::Operand(tempRes1,Type::Float),
                                                     ir::Operator::fneq));
                string tempRes2="t"+ std::to_string(tmp_cnt++);
                buffer.push_back(new ir::Instruction(ir::Operand(tempRes1,Type::Float),
                                                     ir::Operand(),
                                                     ir::Operand(tempRes2,Type::Int),
                                                     ir::Operator::cvt_f2i));
                cond->v=tempRes2;
                cond->t=Type::Int;
            }
            //跳转指令
            buffer.push_back(new ir::Instruction(ir::Operand(cond->v,cond->t),
                                                 ir::Operand(),
                                                 ir::Operand("2",Type::IntLiteral),
                                                 ir::Operator::_goto));
            //if新建作用域 注意：指令未必执行
            symbol_table.add_scope("if");
            vector<ir::Instruction*> ifInstructions;
            analysisStmt(dynamic_cast<Stmt*>(root->children[4]),ifInstructions);
            symbol_table.exit_scope();
            //是否有else判断
            if (int(root->children.size())==7){
                //else新建作用域 注意：指令未必执行
                symbol_table.add_scope("else");
                vector<ir::Instruction*> elseInstructions;
                analysisStmt(dynamic_cast<Stmt*>(root->children[6]),elseInstructions);
                symbol_table.exit_scope();
                //if跳转
                ifInstructions.push_back(new ir::Instruction(ir::Operand(),
                                                             ir::Operand(),
                                                             ir::Operand(std::to_string(int(elseInstructions.size())+1),Type::IntLiteral),
                                                             ir::Operator::_goto));
                //else跳转
                buffer.push_back(new ir::Instruction(ir::Operand(),
                                                     ir::Operand(),
                                                     ir::Operand(std::to_string(int(ifInstructions.size())+1),Type::IntLiteral),
                                                     ir::Operator::_goto));
                buffer.insert(buffer.end(),ifInstructions.begin(),ifInstructions.end());
                buffer.insert(buffer.end(),elseInstructions.begin(),elseInstructions.end());
                //空指令
                buffer.push_back(new ir::Instruction(ir::Operand(),
                                                     ir::Operand(),
                                                     ir::Operand(),
                                                     ir::Operator::__unuse__));
            }
            else{
                //非if跳转
                buffer.push_back(new ir::Instruction(ir::Operand(),
                                                     ir::Operand(),
                                                     ir::Operand(std::to_string(int(ifInstructions.size())+1),Type::IntLiteral),
                                                     ir::Operator::_goto));
                buffer.insert(buffer.end(),ifInstructions.begin(),ifInstructions.end());
                //空指令
                buffer.push_back(new ir::Instruction(ir::Operand(),
                                                     ir::Operand(),
                                                     ir::Operand(),
                                                     ir::Operator::__unuse__));
            }
        }
        //while
        else if (term->token.type==TokenType::WHILETK){
            auto* cond=dynamic_cast<Cond*>(root->children[2]);
            vector<ir::Instruction*> condInstructions;
            analysisCond(cond,condInstructions);
            //cond的值转为整数
            if (cond->t==Type::FloatLiteral){
                cond->v= std::to_string(std::stof(cond->v)!=0);
                cond->t=Type::IntLiteral;
            }
            if (cond->t==Type::Float){
                string tempRes1="t"+ std::to_string(tmp_cnt++);
                condInstructions.push_back(new ir::Instruction(ir::Operand(cond->v,Type::Float),
                                                     ir::Operand("0.0",Type::FloatLiteral),
                                                     ir::Operand(tempRes1,Type::Float),
                                                     ir::Operator::fneq));
                string tempRes2="t"+ std::to_string(tmp_cnt++);
                condInstructions.push_back(new ir::Instruction(ir::Operand(tempRes1,Type::Float),
                                                     ir::Operand(),
                                                     ir::Operand(tempRes2,Type::Int),
                                                     ir::Operator::cvt_f2i));
                cond->v=tempRes2;
                cond->t=Type::Int;
            }
            //stmt新增作用域
            symbol_table.add_scope("while");
            vector<ir::Instruction*> stmtInstructions;
            analysisStmt(dynamic_cast<Stmt*>(root->children[4]),stmtInstructions);
            symbol_table.exit_scope();
            buffer.insert(buffer.end(),condInstructions.begin(),condInstructions.end());
            //进入while中
            buffer.push_back(new ir::Instruction(ir::Operand(cond->v,cond->t),
                                                 ir::Operand(),
                                                 ir::Operand("2",Type::IntLiteral),
                                                 ir::Operator::_goto));
            //while结束添加continue回到开头
            stmtInstructions.push_back(new ir::Instruction(ir::Operand("continue",Type::null),
                                                           ir::Operand(),
                                                           ir::Operand(),
                                                           ir::Operator::__unuse__));
            //跳出while
            buffer.push_back(new ir::Instruction(ir::Operand(),
                                                 ir::Operand(),
                                                 ir::Operand(std::to_string(int(stmtInstructions.size())+1),Type::IntLiteral),
                                                 ir::Operator::_goto));
            //修改break和continue代表的指令
            for (int i=0;i<int(stmtInstructions.size());i++){
                if (stmtInstructions[i]->op1.type==Type::null&&stmtInstructions[i]->op==Operator::__unuse__){
                    if (stmtInstructions[i]->op1.name=="break"){
                        stmtInstructions[i]=new ir::Instruction(ir::Operand(),
                                                                ir::Operand(),
                                                                ir::Operand(std::to_string(int(stmtInstructions.size())-i),Type::IntLiteral),
                                                                ir::Operator::_goto);
                    }
                    else if (stmtInstructions[i]->op1.name=="continue"){
                        stmtInstructions[i]=new ir::Instruction(ir::Operand(),
                                                                ir::Operand(),
                                                                ir::Operand(std::to_string(-(i+2+int(condInstructions.size()))),Type::IntLiteral),
                                                                ir::Operator::_goto);
                    }
                }
            }
            buffer.insert(buffer.end(),stmtInstructions.begin(),stmtInstructions.end());
            //空指令
            buffer.push_back(new ir::Instruction(ir::Operand(),
                                                 ir::Operand(),
                                                 ir::Operand(),
                                                 ir::Operator::__unuse__));
        }
        //break
        else if (term->token.type==TokenType::BREAKTK){
            //新增标记指令
            buffer.push_back(new ir::Instruction(ir::Operand("break",Type::null),
                                                 ir::Operand(),
                                                 ir::Operand(),
                                                 ir::Operator::__unuse__));
        }
        //continue
        else if (term->token.type==TokenType::CONTINUETK){
            //新增标记指令
            buffer.push_back(new ir::Instruction(ir::Operand("continue",Type::null),
                                                 ir::Operand(),
                                                 ir::Operand(),
                                                 ir::Operator::__unuse__));
        }
        //return
        else if (term->token.type==TokenType::RETURNTK){
            if (root->children.size()==3){
                auto* returnExp=dynamic_cast<Exp*>(root->children[1]);
                analysisExp(returnExp,buffer);
                if (symbol_table.functions["__cur__"]->returnType==Type::Int){
                    if (returnExp->t==Type::Int||returnExp->t==Type::IntLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(returnExp->v,returnExp->t),
                                                             ir::Operand(),
                                                             ir::Operand(),
                                                             ir::Operator::_return));
                    }
                    else if (returnExp->t==Type::FloatLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(std::stoi(returnExp->v)),Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(),
                                                             ir::Operator::_return));
                    }
                    else if (returnExp->t==Type::Float){
                        string tempRes="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(returnExp->v,Type::Float),
                                                             ir::Operand(),
                                                             ir::Operand(tempRes,Type::Int),
                                                             ir::Operator::cvt_f2i));
                        buffer.push_back(new ir::Instruction(ir::Operand(tempRes,Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(),
                                                             ir::Operator::_return));
                    }
                    else{
                        assert(0 && "Error in stmt!");
                    }
                }
                else if (symbol_table.functions["__cur__"]->returnType==Type::Float){
                    if (returnExp->t==Type::Float||returnExp->t==Type::FloatLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(returnExp->v,returnExp->t),
                                                             ir::Operand(),
                                                             ir::Operand(),
                                                             ir::Operator::_return));
                    }
                    else if (returnExp->t==Type::IntLiteral){
                        buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(std::stof(returnExp->v)),Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(),
                                                             ir::Operator::_return));
                    }
                    else if (returnExp->t==Type::Int){
                        string tempRes="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(returnExp->v,Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempRes,Type::Float),
                                                             ir::Operator::cvt_i2f));
                        buffer.push_back(new ir::Instruction(ir::Operand(tempRes,Type::Float),
                                                             ir::Operand(),
                                                             ir::Operand(),
                                                             ir::Operator::_return));
                    }
                    else{
                        assert(0 && "Error in stmt!");
                    }
                }
                else{
                    assert(0 && "Error in stmt!");
                }
            }
            else{
                buffer.push_back(new ir::Instruction(ir::Operand(),
                                                     ir::Operand(),
                                                     ir::Operand(),
                                                     ir::Operator::_return));
            }
        }
        // ;
        else{
            ;
        }
    }
}

void frontend::Analyzer::analysisExp(frontend::Exp* root,vector<ir::Instruction*>& buffer){
    //Exp -> AddExp
    //Exp.is_computable
    //Exp.v
    //Exp.t

    auto addExp=dynamic_cast<AddExp*>(root->children[0]);
    analysisAddExp(addExp,buffer);
    root->t=addExp->t;
    root->v=addExp->v;
    root->is_computable=addExp->is_computable;
}

void frontend::Analyzer::analysisCond(frontend::Cond* root,vector<ir::Instruction*>& buffer){
    //Cond -> LOrExp
    //Cond.is_computable
    //Cond.v
    //Cond.t

    auto lOrExp=dynamic_cast<LOrExp*>(root->children[0]);
    analysisLOrExp(lOrExp,buffer);
    root->t=lOrExp->t;
    root->v=lOrExp->v;
    root->is_computable=lOrExp->is_computable;
}

void frontend::Analyzer::analysisLVal(frontend::LVal* root,vector<ir::Instruction*>& buffer,string& varName,ir::Operand& offset){
    //LVal -> Ident {'[' Exp ']'}
    //LVal.is_computable
    //LVal.v
    //LVal.t
    //LVal.i

    //确定变量名
    varName=dynamic_cast<Term*>(root->children[0])->token.value;
    //判断变量是否是数组（最多二维）
    if (int(root->children.size())==1){
        STE ste=symbol_table.get_ste(varName);
        root->t=ste.operand.type;
        offset.name="-1";
        offset.type=Type::IntLiteral;
        if (root->t==Type::IntLiteral||root->t==Type::FloatLiteral){
            root->v=ste.literalValue;
        }
        else {
            root->v = ste.operand.name;
        }
    }
    else if (int(root->children.size())==4){
        //分析exp
        auto exp=dynamic_cast<Exp*>(root->children[2]);
        analysisExp(exp,buffer);
        STE ste=symbol_table.get_ste(varName);
        //一维数组
        if (int(ste.dimension.size())==1){
            offset.name=exp->v;
            offset.type=exp->t;
            Type require;
            if (ste.operand.type==Type::IntPtr){
                require=Type::Int;
            }
            else{
                require=Type::Float;
            }
            string tempVar="t"+ std::to_string(tmp_cnt++);
            buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ste.operand.type),
                                                 ir::Operand(exp->v,exp->t),
                                                 ir::Operand(tempVar,require),
                                                 ir::Operator::load));
            root->t=require;
            root->v=tempVar;
        }
        //二维数组
        else{
            Type require=ste.operand.type;
            string tempVar="t"+ std::to_string(tmp_cnt++);
            //计算偏移
            if (exp->t==Type::IntLiteral){
                offset.name= std::to_string(std::stoi(exp->v)*ste.dimension[1]);
                offset.type=Type::IntLiteral;
                buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ste.operand.type),
                                                     ir::Operand(offset.name,Type::IntLiteral),
                                                     ir::Operand(tempVar,require),
                                                     ir::Operator::getptr));
            }
            else{
                string tempOffset="t"+ std::to_string(tmp_cnt++);
                string tempMulOpt="t"+ std::to_string(tmp_cnt++);
                buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(ste.dimension[1]),Type::IntLiteral),
                                                     ir::Operand(),
                                                     ir::Operand(tempMulOpt,Type::Int),
                                                     ir::Operator::def));
                buffer.push_back(new ir::Instruction(ir::Operand(exp->v,Type::Int),
                                                     ir::Operand(tempMulOpt,Type::Int),
                                                     ir::Operand(tempOffset,Type::Int),
                                                     ir::Operator::mul));
                buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ste.operand.type),
                                                     ir::Operand(tempOffset,Type::Int),
                                                     ir::Operand(tempVar,require),
                                                     ir::Operator::getptr));
                offset.name=tempOffset;
                offset.type=Type::Int;
            }
            root->v=tempVar;
            root->t=require;
        }
    }
    else if (int(root->children.size())==7){
        //分析exp
        auto exp1=dynamic_cast<Exp*>(root->children[2]);
        auto exp2=dynamic_cast<Exp*>(root->children[5]);
        analysisExp(exp1,buffer);
        analysisExp(exp2,buffer);
        STE ste=symbol_table.get_ste(varName);
        Type require;
        if (ste.operand.type==Type::IntPtr){
            require=Type::Int;
        }
        else{
            require=Type::Float;
        }
        //记录2个维度
        string tempDim1="t"+ std::to_string(tmp_cnt++);
        string tempDim2="t"+ std::to_string(tmp_cnt++);
        buffer.push_back(new ir::Instruction(ir::Operand(exp1->v,exp1->t),
                                             ir::Operand(),
                                             ir::Operand(tempDim1,Type::Int),
                                             ir::Operator::def));
        buffer.push_back(new ir::Instruction(ir::Operand(exp2->v,exp2->t),
                                             ir::Operand(),
                                             ir::Operand(tempDim2,Type::Int),
                                             ir::Operator::def));
        //记录列数
        string tempCol="t"+ std::to_string(tmp_cnt++);
        buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(ste.dimension[1]),Type::IntLiteral),
                                             ir::Operand(),
                                             ir::Operand(tempCol,Type::Int),
                                             ir::Operator::def));
        //计算第1维的偏移
        string tempOffset1="t"+ std::to_string(tmp_cnt++);
        buffer.push_back(new ir::Instruction(ir::Operand(tempDim1,Type::Int),
                                             ir::Operand(tempCol,Type::Int),
                                             ir::Operand(tempOffset1,Type::Int),
                                             ir::Operator::mul));
        //计算第2维的偏移
        string tempOffset2="t"+ std::to_string(tmp_cnt++);
        buffer.push_back(new ir::Instruction(ir::Operand(tempOffset1,Type::Int),
                                             ir::Operand(tempDim2,Type::Int),
                                             ir::Operand(tempOffset2,Type::Int),
                                             ir::Operator::add));
        //取值
        string requireName="t"+ std::to_string(tmp_cnt++);
        buffer.push_back(new ir::Instruction(ir::Operand(ste.operand.name,ste.operand.type),
                                             ir::Operand(tempOffset2,Type::Int),
                                             ir::Operand(requireName,require),
                                             ir::Operator::load));
        offset.name=tempOffset2;
        offset.type=Type::Int;
        root->v=requireName;
        root->t=require;
    }
}

void frontend::Analyzer::analysisNumber(frontend::Number* root,vector<ir::Instruction*>& buffer){
    //Number -> IntConst | floatConst

    Term* term=dynamic_cast<Term*>(root->children[0]);
    if (term->token.type==TokenType::INTLTR){
        root->t=Type::IntLiteral;
        string s=term->token.value;
        //判断进制
        //十六进制
        if (int(s.length())>=3&&s[0]=='0'&&(s[1]=='x'||s[1]=='X')){
            root->v= std::to_string(std::stoi(s.substr(2),nullptr,16));
        }
        //二进制
        else if (int(s.length())>=3&&s[0]=='0'&&(s[1]=='b'||s[1]=='B')){
            root->v= std::to_string(std::stoi(s.substr(2), nullptr,2));
        }
        //八进制
        else if (int(s.length())>=2&&s[0]=='0'){
            root->v= std::to_string(std::stoi(s.substr(1), nullptr,8));
        }
        //十进制
        else{
            root->v=s;
        }
    }
    else if (term->token.type==TokenType::FLOATLTR){
        root->t=Type::FloatLiteral;
        root->v=term->token.value;
    }
    else{
        assert(0 && "Error in number!");
    }
}

void frontend::Analyzer::analysisPrimaryExp(frontend::PrimaryExp* root,vector<ir::Instruction*>& buffer){
    //PrimaryExp -> '(' Exp ')' | LVal | Number
    //PrimaryExp.is_computable
    //PrimaryExp.v
    //PrimaryExp.t

    if (int(root->children.size())==3){
        auto* exp=dynamic_cast<Exp*>(root->children[1]);
        analysisExp(exp,buffer);
        root->t=exp->t;
        root->v=exp->v;
        root->is_computable=exp->is_computable;
    }
    else if (auto* lVal=dynamic_cast<LVal*>(root->children[0])){
        string varName;
        ir::Operand offset;
        analysisLVal(lVal,buffer,varName,offset);
        root->v=lVal->v;
        root->t=lVal->t;
        root->is_computable=lVal->is_computable;
    }
    else if (auto* number=dynamic_cast<Number*>(root->children[0])){
        analysisNumber(number,buffer);
        root->v=number->v;
        root->t=number->t;
        root->is_computable=number->is_computable;
    }
    else{
        assert(0 && "Error in primaryexp!");
    }
}

void frontend::Analyzer::analysisUnaryExp(frontend::UnaryExp* root,vector<ir::Instruction*>& buffer){
    //UnaryExp -> PrimaryExp | Ident '(' [FuncRParams] ')' | UnaryOp UnaryExp
    //UnaryExp.is_computable
    //UnaryExp.v
    //UnaryExp.t

    if (auto* primaryExp=dynamic_cast<PrimaryExp*>(root->children[0])){
        analysisPrimaryExp(primaryExp,buffer);
        root->v=primaryExp->v;
        root->t=primaryExp->t;
        root->is_computable=primaryExp->is_computable;
    }
    //Ident分支 进行函数调用
    else if (auto* term=dynamic_cast<Term*>(root->children[0])){
        string funcName=term->token.value;
        vector<Operand> params;
        Function* func=symbol_table.functions[funcName];
        //如果有参数则进行分析
        if (int(root->children.size())==4){
            vector<Operand> primitiveParams;
            auto* funcRParams=dynamic_cast<FuncRParams*>(root->children[2]);
            analysisFuncRParams(funcRParams,buffer,primitiveParams);
            vector<Operand> funcParams=func->ParameterList;
            if (int(primitiveParams.size())!=int(funcParams.size())){
                assert(0 && "Error in unaryexp!");
            }
            for (int i=0;i<int(primitiveParams.size());i++){
                //类型提升
                if (funcParams[i].type==Type::Float){
                    if (primitiveParams[i].type==Type::Int){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(primitiveParams[i].name,ir::Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Float),
                                                             ir::Operator::cvt_i2f));
                        params.emplace_back(Operand(tempName,Type::Float));
                    }
                    else if (primitiveParams[i].type==Type::IntLiteral){
                        params.emplace_back(Operand(std::to_string(std::stof(primitiveParams[i].name)),ir::Type::FloatLiteral));
                    }
                    else{
                        params.emplace_back(primitiveParams[i]);
                    }
                }
                else if (funcParams[i].type==Type::Int){
                    if (primitiveParams[i].type==Type::Float){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(primitiveParams[i].name,Type::Float),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Int),
                                                             ir::Operator::cvt_f2i));
                        params.emplace_back(Operand(tempName,ir::Type::Int));
                    }
                    else if (primitiveParams[i].type==Type::FloatLiteral){
                        params.emplace_back(Operand(std::to_string(std::stoi(primitiveParams[i].name)),Type::IntLiteral));
                    }
                    else{
                       params.emplace_back(primitiveParams[i]);
                    }
                }
                else{
                    params.emplace_back(primitiveParams[i]);
                }
            }
        }
        string tempFuncRes="t"+ std::to_string(tmp_cnt++);
        buffer.push_back(new ir::CallInst(ir::Operand(func->name,func->returnType),
                                          params,
                                          ir::Operand(tempFuncRes,func->returnType)));
        root->v=tempFuncRes;
        root->t=func->returnType;
    }
    //UnaryOp分支
    else{
        TokenType tokenType;
        analysisUnaryOp(dynamic_cast<UnaryOp*>(root->children[0]),tokenType);
        auto* unaryExp=dynamic_cast<UnaryExp*>(root->children[1]);
        analysisUnaryExp(unaryExp,buffer);
        if (tokenType==TokenType::PLUS){
            root->v=unaryExp->v;
            root->t=unaryExp->t;
            root->is_computable=unaryExp->is_computable;
        }
        else if (tokenType==TokenType::MINU){
            if (unaryExp->t==Type::FloatLiteral){
                root->v= std::to_string(-std::stof(unaryExp->v));
                root->t=Type::FloatLiteral;
                root->is_computable=true;
            }
            else if (unaryExp->t==Type::IntLiteral){
                root->v= std::to_string(-std::stoi(unaryExp->v));
                root->t=Type::IntLiteral;
                root->is_computable=true;
            }
            else if (unaryExp->t==Type::Int){
                string tempZero="t"+ std::to_string(tmp_cnt++);
                string tempRes="t"+ std::to_string(tmp_cnt++);
                buffer.push_back(new ir::Instruction(ir::Operand("0",Type::IntLiteral),
                                                     ir::Operand(),
                                                     ir::Operand(tempZero,Type::Int),
                                                     ir::Operator::def));
                buffer.push_back(new ir::Instruction(ir::Operand(tempZero,Type::Int),
                                                     ir::Operand(unaryExp->v,Type::Int),
                                                     ir::Operand(tempRes,Type::Int),
                                                     ir::Operator::sub));
                root->v=tempRes;
                root->t=Type::Int;
            }
            else{
                string tempZero="t"+ std::to_string(tmp_cnt++);
                string tempRes="t"+ std::to_string(tmp_cnt++);
                buffer.push_back(new ir::Instruction(ir::Operand("0.0",Type::FloatLiteral),
                                                     ir::Operand(),
                                                     ir::Operand(tempZero,Type::Float),
                                                     ir::Operator::fdef));
                buffer.push_back(new ir::Instruction(ir::Operand(tempZero,Type::Float),
                                                     ir::Operand(unaryExp->v,Type::Float),
                                                     ir::Operand(tempRes,Type::Float),
                                                     ir::Operator::fsub));
                root->v=tempRes;
                root->t=Type::Float;
            }
        }
        //Token:!
        else{
            if (unaryExp->t==Type::FloatLiteral){
                root->v= std::to_string(!std::stof(unaryExp->v));
                root->t=Type::IntLiteral;
                root->is_computable=true;
            }
            else if (unaryExp->t==Type::IntLiteral){
                root->v= std::to_string(!std::stoi(unaryExp->v));
                root->t=Type::IntLiteral;
                root->is_computable=true;
            }
            else if (unaryExp->t==Type::Int){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                buffer.push_back(new ir::Instruction(ir::Operand(unaryExp->v,Type::Int),
                                                     ir::Operand(),
                                                     ir::Operand(tempRes,Type::Int),
                                                     ir::Operator::_not));
                root->v=tempRes;
                root->t=Type::Int;
                root->is_computable=false;
            }
            else{  //Float
                string tempRes="t"+ std::to_string(tmp_cnt++);
                buffer.push_back(new ir::Instruction(ir::Operand(unaryExp->v,Type::Float),
                                                     ir::Operand(),
                                                     ir::Operand(tempRes,Type::Int),
                                                     ir::Operator::_not));
                root->v=tempRes;
                root->t=Type::Int;
                root->is_computable=false;
            }
        }
    }
}

void frontend::Analyzer::analysisUnaryOp(frontend::UnaryOp* root,TokenType& buffer){
    //UnaryOp -> '+' | '-' | '!'

    auto term=dynamic_cast<Term*>(root->children[0]);
    buffer=term->token.type;
}

void frontend::Analyzer::analysisFuncRParams(frontend::FuncRParams* root,vector<ir::Instruction*>& buffer,vector<ir::Operand>& params){
    //FuncRParams -> Exp { ',' Exp }

    for (int i=0;i<int(root->children.size());i+=2){
        auto* exp=dynamic_cast<Exp*>(root->children[i]);
        analysisExp(exp,buffer);
        params.emplace_back(ir::Operand(exp->v,exp->t));
    }
}

void frontend::Analyzer::analysisMulExp(frontend::MulExp* root,vector<ir::Instruction*>& buffer){
    //MulExp -> UnaryExp { ('*' | '/' | '%') UnaryExp }
    //MulExp.is_computable
    //MulExp.v
    //MulExp.t

    bool intFlag=true;
    root->is_computable=true;
    for (int i=0;i<int(root->children.size());i+=2){
        auto* unaryExp=dynamic_cast<UnaryExp*>(root->children[i]);
        analysisUnaryExp(unaryExp,buffer);
        root->is_computable=root->is_computable&&unaryExp->is_computable;
        if (unaryExp->t!=Type::IntLiteral){
            intFlag=false;
        }
    }
    //常量直接计算
    if (root->is_computable){
        if (intFlag){
            int res=std::stoi(dynamic_cast<UnaryExp*>(root->children[0])->v);
            for (int i=2;i<int(root->children.size());i+=2){
                auto* term = dynamic_cast<Term *>(root->children[i - 1]);
                if (term->token.type==TokenType::MULT){
                    res*=std::stoi(dynamic_cast<UnaryExp*>(root->children[i])->v);
                }
                else if (term->token.type==TokenType::DIV){
                    res/=std::stoi(dynamic_cast<UnaryExp*>(root->children[i])->v);
                }
                else if (term->token.type==TokenType::MOD){
                    res%=std::stoi(dynamic_cast<UnaryExp*>(root->children[i])->v);
                }
                else{
                    assert(0 && "Error in mulexp!");
                }
            }
            root->v= std::to_string(res);
            root->t=Type::IntLiteral;
        }
        else{
            float res=std::stof(dynamic_cast<UnaryExp*>(root->children[0])->v);
            for (int i=2;i<int(root->children.size());i+=2){
                auto* term = dynamic_cast<Term *>(root->children[i - 1]);
                if (term->token.type==TokenType::MULT){
                    res*=std::stof(dynamic_cast<UnaryExp*>(root->children[i])->v);
                }
                else if (term->token.type==TokenType::DIV){
                    res/=std::stof(dynamic_cast<UnaryExp*>(root->children[i])->v);
                }
                else{
                    assert(0 && "Error in mulexp!");
                }
            }
            root->v= std::to_string(res);
            root->t=Type::FloatLiteral;
        }
        return;
    }
    //计算表达式的结果
    root->t=dynamic_cast<UnaryExp*>(root->children[0])->t;
    root->v=dynamic_cast<UnaryExp*>(root->children[0])->v;
    if (int(root->children.size())>1){
        //确定类型
        for (int i=2;i<int(root->children.size());i+=2) {
            auto unaryExp = dynamic_cast<UnaryExp *>(root->children[i]);
            auto term = dynamic_cast<Term *>(root->children[i - 1]);
            Type ultimateType = root->t;
            if (root->t != unaryExp->t) {
                if (unaryExp->t == Type::Float) {
                    ultimateType = Type::Float;
                } else if (unaryExp->t == Type::Int && ultimateType == Type::IntLiteral) {
                    ultimateType = Type::Int;
                } else if (unaryExp->t == Type::FloatLiteral && ultimateType == Type::IntLiteral) {
                    ultimateType = Type::FloatLiteral;
                } else if ((unaryExp->t == Type::FloatLiteral && ultimateType == Type::Int) ||
                           (unaryExp->t == Type::Int && ultimateType == Type::FloatLiteral)) {
                    ultimateType = Type::Float;
                }
                //类型转换
                if (ultimateType == Type::Int) {
                    if (unaryExp->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(unaryExp->v, Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Int),
                                                             ir::Operator::def));
                        unaryExp->v = tempName;
                        unaryExp->t = Type::Int;
                    }
                    if (root->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Int),
                                                             ir::Operator::def));
                        root->v = tempName;
                        root->t = Type::Int;
                    }
                } else if (ultimateType == Type::FloatLiteral) {
                    if (unaryExp->t == Type::IntLiteral) {
                        unaryExp->v = std::to_string(std::stof(unaryExp->v));
                        unaryExp->t = Type::FloatLiteral;
                    }
                    if (root->t == Type::IntLiteral) {
                        root->v = std::to_string(std::stof(root->v));
                        root->t = Type::FloatLiteral;
                    }
                } else if (ultimateType == Type::Float) {
                    if (unaryExp->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(
                                ir::Operand(std::to_string(std::stof(unaryExp->v)), Type::FloatLiteral),
                                ir::Operand(),
                                ir::Operand(tempName, Type::Float),
                                ir::Operator::fdef));
                        unaryExp->v = tempName;
                        unaryExp->t = Type::Float;
                    }
                    if (unaryExp->t == Type::Int) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(unaryExp->v, Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::cvt_i2f));
                        unaryExp->v = tempName;
                        unaryExp->t = Type::Float;
                    }
                    if (unaryExp->t == Type::FloatLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(unaryExp->v, Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::fdef));
                        unaryExp->v = tempName;
                        unaryExp->t = Type::Float;
                    }
                    if (root->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(
                                new ir::Instruction(ir::Operand(std::to_string(std::stof(root->v)), Type::FloatLiteral),
                                                    ir::Operand(),
                                                    ir::Operand(tempName, Type::Float),
                                                    ir::Operator::fdef));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                    if (root->t == Type::Int) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::cvt_i2f));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                    if (root->t == Type::FloatLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::fdef));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                }
            }
            //类型相同后开始计算
            if (ultimateType==Type::IntLiteral){
                if (term->token.type==TokenType::MULT){
                    root->v= std::to_string(std::stoi(root->v)* std::stoi(unaryExp->v));
                }
                else if (term->token.type==TokenType::DIV){
                    root->v= std::to_string(std::stoi(root->v)/ std::stoi(unaryExp->v));
                }
                else{
                    root->v= std::to_string(std::stoi(root->v)% std::stoi(unaryExp->v));
                }
            }
            else if (ultimateType==Type::FloatLiteral){
                if (term->token.type==TokenType::MULT){
                    root->v= std::to_string(std::stof(root->v)* std::stof(unaryExp->v));
                }
                else if (term->token.type==TokenType::DIV){
                    root->v= std::to_string(std::stof(root->v)/ std::stof(unaryExp->v));
                }
                else{
                    //浮点不进行mod运算
                    assert(0 && "No mod in float!");
                }
            }
            else if (ultimateType==Type::Int){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                if (term->token.type==TokenType::MULT){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(unaryExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::mul));
                }
                else if (term->token.type==TokenType::DIV){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(unaryExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::div));
                }
                else{  //MOD
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(unaryExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::mod));
                }
                root->v=tempRes;
            }
            else if (ultimateType==Type::Float){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                if (term->token.type==TokenType::MULT){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(unaryExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::fmul));
                }
                else if (term->token.type==TokenType::DIV){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(unaryExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::fdiv));
                }
                else{
                    //浮点数不进行mod运算
                    assert(0 && "No mod in float!");
                }
                root->v=tempRes;
            }
        }
    }
}

void frontend::Analyzer::analysisAddExp(frontend::AddExp* root,vector<ir::Instruction*>& buffer){
    //AddExp -> MulExp { ('+' | '-') MulExp }
    //AddExp.is_computable
    //AddExp.v
    //AddExp.t

    bool intFlag=true;
    root->is_computable=true;
    for (int i=0;i<int(root->children.size());i+=2){
        auto* mulExp=dynamic_cast<MulExp*>(root->children[i]);
        analysisMulExp(mulExp,buffer);
        root->is_computable=root->is_computable&&mulExp->is_computable;
        if (mulExp->t!=Type::IntLiteral){
            intFlag=false;
        }
    }
    //常量直接计算
    if (root->is_computable){
        if (intFlag){
            int res=std::stoi(dynamic_cast<MulExp*>(root->children[0])->v);
            for (int i=2;i<int(root->children.size());i+=2){
                auto* term = dynamic_cast<Term *>(root->children[i - 1]);
                if (term->token.type==TokenType::PLUS){
                    res+=std::stoi(dynamic_cast<MulExp*>(root->children[i])->v);
                }
                else if (term->token.type==TokenType::MINU){
                    res-=std::stoi(dynamic_cast<MulExp*>(root->children[i])->v);
                }
                else{
                    assert(0 && "Error in addexp!");
                }
            }
            root->v= std::to_string(res);
            root->t=Type::IntLiteral;
        }
        else{
            float res=std::stof(dynamic_cast<MulExp*>(root->children[0])->v);
            for (int i=2;i<int(root->children.size());i+=2){
                auto* term = dynamic_cast<Term *>(root->children[i - 1]);
                if (term->token.type==TokenType::PLUS){
                    res+=std::stof(dynamic_cast<MulExp*>(root->children[i])->v);
                }
                else if (term->token.type==TokenType::MINU){
                    res-=std::stof(dynamic_cast<MulExp*>(root->children[i])->v);
                }
                else{
                    assert(0 && "Error in mulexp!");
                }
            }
            root->v= std::to_string(res);
            root->t=Type::FloatLiteral;
        }
        return;
    }
    //计算表达式的结果
    root->t=dynamic_cast<MulExp*>(root->children[0])->t;
    root->v=dynamic_cast<MulExp*>(root->children[0])->v;
    if (int(root->children.size())>1){
        //确定类型
        for (int i=2;i<int(root->children.size());i+=2) {
            auto mulExp = dynamic_cast<MulExp *>(root->children[i]);
            auto term = dynamic_cast<Term *>(root->children[i - 1]);
            Type ultimateType = root->t;
            if (root->t != mulExp->t) {
                if (mulExp->t == Type::Float) {
                    ultimateType = Type::Float;
                } else if (mulExp->t == Type::Int && ultimateType == Type::IntLiteral) {
                    ultimateType = Type::Int;
                } else if (mulExp->t == Type::FloatLiteral && ultimateType == Type::IntLiteral) {
                    ultimateType = Type::FloatLiteral;
                } else if ((mulExp->t == Type::FloatLiteral && ultimateType == Type::Int) ||
                           (mulExp->t == Type::Int && ultimateType == Type::FloatLiteral)) {
                    ultimateType = Type::Float;
                }
                //类型转换
                if (ultimateType == Type::Int) {
                    if (mulExp->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(mulExp->v, Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Int),
                                                             ir::Operator::def));
                        mulExp->v = tempName;
                        mulExp->t = Type::Int;
                    }
                    if (root->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Int),
                                                             ir::Operator::def));
                        root->v = tempName;
                        root->t = Type::Int;
                    }
                } else if (ultimateType == Type::FloatLiteral) {
                    if (mulExp->t == Type::IntLiteral) {
                        mulExp->v = std::to_string(std::stof(mulExp->v));
                        mulExp->t = Type::FloatLiteral;
                    }
                    if (root->t == Type::IntLiteral) {
                        root->v = std::to_string(std::stof(root->v));
                        root->t = Type::FloatLiteral;
                    }
                } else if (ultimateType == Type::Float) {
                    if (mulExp->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(
                                ir::Operand(std::to_string(std::stof(mulExp->v)), Type::FloatLiteral),
                                ir::Operand(),
                                ir::Operand(tempName, Type::Float),
                                ir::Operator::fdef));
                        mulExp->v = tempName;
                        mulExp->t = Type::Float;
                    }
                    if (mulExp->t == Type::Int) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(mulExp->v, Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::cvt_i2f));
                        mulExp->v = tempName;
                        mulExp->t = Type::Float;
                    }
                    if (mulExp->t == Type::FloatLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(mulExp->v, Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::fdef));
                        mulExp->v = tempName;
                        mulExp->t = Type::Float;
                    }
                    if (root->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(
                                new ir::Instruction(ir::Operand(std::to_string(std::stof(root->v)), Type::FloatLiteral),
                                                    ir::Operand(),
                                                    ir::Operand(tempName, Type::Float),
                                                    ir::Operator::fdef));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                    if (root->t == Type::Int) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::cvt_i2f));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                    if (root->t == Type::FloatLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::fdef));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                }
            }
            //类型相同后开始计算
            if (ultimateType==Type::IntLiteral){
                if (term->token.type==TokenType::PLUS){
                    root->v= std::to_string(std::stoi(root->v)+ std::stoi(mulExp->v));
                }
                else{
                    root->v= std::to_string(std::stoi(root->v)- std::stoi(mulExp->v));
                }
            }
            else if (ultimateType==Type::FloatLiteral){
                if (term->token.type==TokenType::PLUS){
                    root->v= std::to_string(std::stof(root->v)+ std::stof(mulExp->v));
                }
                else{
                    root->v= std::to_string(std::stof(root->v)- std::stof(mulExp->v));
                }
            }
            else if (ultimateType==Type::Int){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                if (term->token.type==TokenType::PLUS){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(mulExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::add));
                }
                else{
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(mulExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::sub));
                }
                root->v=tempRes;
            }
            else if (ultimateType==Type::Float){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                if (term->token.type==TokenType::PLUS){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(mulExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::fadd));
                }
                else{
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(mulExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::fsub));
                }
                root->v=tempRes;
            }
        }
    }
}

void frontend::Analyzer::analysisRelExp(frontend::RelExp* root,vector<ir::Instruction*>& buffer){
    //RelExp -> AddExp { ('<' | '>' | '<=' | '>=') AddExp }
    //RelExp.is_computable
    //RelExp.v
    //RelExp.t

    bool intFlag=true;
    root->is_computable=true;
    for (int i=0;i<int(root->children.size());i+=2){
        auto* addExp=dynamic_cast<AddExp*>(root->children[i]);
        analysisAddExp(addExp,buffer);
        root->is_computable=root->is_computable&&addExp->is_computable;
        if (addExp->t!=Type::IntLiteral){
            intFlag=false;
        }
    }
    //常量直接计算
    if (root->is_computable){
        if (intFlag){
            int res=std::stoi(dynamic_cast<AddExp*>(root->children[0])->v);
            for (int i=2;i<int(root->children.size());i+=2){
                auto* term = dynamic_cast<Term *>(root->children[i - 1]);
                if (term->token.type==TokenType::LSS){
                    res=(res<std::stoi(dynamic_cast<AddExp*>(root->children[i])->v));
                }
                else if (term->token.type==TokenType::GTR){
                    res=(res>std::stoi(dynamic_cast<AddExp*>(root->children[i])->v));
                }
                else if (term->token.type==TokenType::LEQ){
                    res=(res<=std::stoi(dynamic_cast<AddExp*>(root->children[i])->v));
                }
                else if (term->token.type==TokenType::GEQ){
                    res=(res>=std::stoi(dynamic_cast<AddExp*>(root->children[i])->v));
                }
                else{
                    assert(0 && "Error in relexp!");
                }
            }
            root->v= std::to_string(res);
            root->t=Type::IntLiteral;
        }
        else{
            float res=std::stof(dynamic_cast<MulExp*>(root->children[0])->v);
            if (int(root->children.size())==1){
                root->v= std::to_string(res);
                root->t=Type::FloatLiteral;
            }
            else{
                for (int i=2;i<int(root->children.size());i+=2){
                    auto* term = dynamic_cast<Term *>(root->children[i - 1]);
                    if (term->token.type==TokenType::LSS){
                        res=(res<std::stof(dynamic_cast<AddExp*>(root->children[i])->v));
                    }
                    else if (term->token.type==TokenType::GTR){
                        res=(res>std::stof(dynamic_cast<AddExp*>(root->children[i])->v));
                    }
                    else if (term->token.type==TokenType::LEQ){
                        res=(res<=std::stof(dynamic_cast<AddExp*>(root->children[i])->v));
                    }
                    else if (term->token.type==TokenType::GEQ){
                        res=(res>=std::stof(dynamic_cast<AddExp*>(root->children[i])->v));
                    }
                    else{
                        assert(0 && "Error in relexp!");
                    }
                }
                root->v= std::to_string(int(res));
                root->t=Type::IntLiteral;
            }
        }
        return;
    }
    //计算表达式的结果
    root->t=dynamic_cast<AddExp*>(root->children[0])->t;
    root->v=dynamic_cast<AddExp*>(root->children[0])->v;
    if (int(root->children.size())>1){
        //确定类型
        for (int i=2;i<int(root->children.size());i+=2) {
            auto addExp = dynamic_cast<AddExp *>(root->children[i]);
            auto term = dynamic_cast<Term *>(root->children[i - 1]);
            Type ultimateType = root->t;
            if (root->t != addExp->t) {
                if (addExp->t == Type::Float) {
                    ultimateType = Type::Float;
                } else if (addExp->t == Type::Int && ultimateType == Type::IntLiteral) {
                    ultimateType = Type::Int;
                } else if (addExp->t == Type::FloatLiteral && ultimateType == Type::IntLiteral) {
                    ultimateType = Type::FloatLiteral;
                } else if ((addExp->t == Type::FloatLiteral && ultimateType == Type::Int) ||
                           (addExp->t == Type::Int && ultimateType == Type::FloatLiteral)) {
                    ultimateType = Type::Float;
                }
                //类型转换
                if (ultimateType == Type::Int) {
                    if (addExp->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(addExp->v, Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Int),
                                                             ir::Operator::def));
                        addExp->v = tempName;
                        addExp->t = Type::Int;
                    }
                    if (root->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Int),
                                                             ir::Operator::def));
                        root->v = tempName;
                        root->t = Type::Int;
                    }
                } else if (ultimateType == Type::FloatLiteral) {
                    if (addExp->t == Type::IntLiteral) {
                        addExp->v = std::to_string(std::stof(addExp->v));
                        addExp->t = Type::FloatLiteral;
                    }
                    if (root->t == Type::IntLiteral) {
                        root->v = std::to_string(std::stof(root->v));
                        root->t = Type::FloatLiteral;
                    }
                } else if (ultimateType == Type::Float) {
                    if (addExp->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(
                                ir::Operand(std::to_string(std::stof(addExp->v)), Type::FloatLiteral),
                                ir::Operand(),
                                ir::Operand(tempName, Type::Float),
                                ir::Operator::fdef));
                        addExp->v = tempName;
                        addExp->t = Type::Float;
                    }
                    if (addExp->t == Type::Int) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(addExp->v, Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::cvt_i2f));
                        addExp->v = tempName;
                        addExp->t = Type::Float;
                    }
                    if (addExp->t == Type::FloatLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(addExp->v, Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::fdef));
                        addExp->v = tempName;
                        addExp->t = Type::Float;
                    }
                    if (root->t == Type::IntLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(
                                new ir::Instruction(ir::Operand(std::to_string(std::stof(root->v)), Type::FloatLiteral),
                                                    ir::Operand(),
                                                    ir::Operand(tempName, Type::Float),
                                                    ir::Operator::fdef));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                    if (root->t == Type::Int) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::cvt_i2f));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                    if (root->t == Type::FloatLiteral) {
                        string tempName = "t" + std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v, Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName, Type::Float),
                                                             ir::Operator::fdef));
                        root->v = tempName;
                        root->t = Type::Float;
                    }
                }
            }
            //类型相同后开始计算
            if (ultimateType==Type::IntLiteral){
                if (term->token.type==TokenType::LSS){
                    root->v= std::to_string(std::stoi(root->v)< std::stoi(addExp->v));
                }
                else if (term->token.type==TokenType::GTR){
                    root->v= std::to_string(std::stoi(root->v)> std::stoi(addExp->v));
                }
                else if (term->token.type==TokenType::LEQ){
                    root->v= std::to_string(std::stoi(root->v)<= std::stoi(addExp->v));
                }
                else{
                    root->v= std::to_string(std::stoi(root->v)>= std::stoi(addExp->v));
                }
            }
            else if (ultimateType==Type::FloatLiteral){
                if (term->token.type==TokenType::LSS){
                    root->v= std::to_string(std::stof(root->v)< std::stof(addExp->v));
                }
                else if (term->token.type==TokenType::GTR){
                    root->v= std::to_string(std::stof(root->v)> std::stof(addExp->v));
                }
                else if (term->token.type==TokenType::LEQ){
                    root->v= std::to_string(std::stof(root->v)<= std::stof(addExp->v));
                }
                else{
                    root->v= std::to_string(std::stof(root->v)>= std::stof(addExp->v));
                }
                root->t=Type::IntLiteral;
            }
            else if (ultimateType==Type::Int){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                if (term->token.type==TokenType::LSS){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(addExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::lss));
                }
                else if (term->token.type==TokenType::GTR){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(addExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::gtr));
                }
                else if (term->token.type==TokenType::LEQ){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(addExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::leq));
                }
                else{
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(addExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::geq));
                }
                root->v=tempRes;
                root->t=Type::Int;
            }
            else if (ultimateType==Type::Float){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                if (term->token.type==TokenType::LSS){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(addExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::flss));
                }
                else if (term->token.type==TokenType::GTR){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(addExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::fgtr));
                }
                else if (term->token.type==TokenType::LEQ){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(addExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::fleq));
                }
                else{
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(addExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::fgeq));
                }
                root->v=tempRes;
                root->t=Type::Float;
            }
        }
    }
}

void frontend::Analyzer::analysisEqExp(frontend::EqExp* root,vector<ir::Instruction*>& buffer){
    //EqExp -> RelExp { ('==' | '!=') RelExp }
    //EqExp.is_computable
    //EqExp.v
    //EqExp.t

    bool intFlag=true;
    root->is_computable=true;
    //计算所有RelExp
    for (int i=0;i<int(root->children.size());i+=2){
        auto* relExp=dynamic_cast<RelExp*>(root->children[i]);
        analysisRelExp(relExp,buffer);
        root->is_computable=root->is_computable&&relExp->is_computable;
        if (relExp->t!=Type::IntLiteral){
            intFlag=false;
        }
    }
    //常量直接计算
    if (root->is_computable){
        if (intFlag){
            int res=std::stoi(dynamic_cast<RelExp*>(root->children[0])->v);
            for (int i=2;i<int(root->children.size());i+=2){
                auto* term = dynamic_cast<Term *>(root->children[i - 1]);
                if (term->token.type==TokenType::EQL){
                    res=(res==std::stoi(dynamic_cast<RelExp*>(root->children[i])->v));
                }
                else if (term->token.type==TokenType::NEQ){
                    res=(res!=std::stoi(dynamic_cast<RelExp*>(root->children[i])->v));
                }
                else{
                    assert(0 && "Error in eqexp!");
                }
            }
            root->v= std::to_string(res);
            root->t=Type::IntLiteral;
        }
        else{
            float res=std::stof(dynamic_cast<RelExp*>(root->children[0])->v);
            if (int(root->children.size())==1){
                root->v= std::to_string(res);
                root->t=Type::FloatLiteral;
            }
            for (int i=2;i<int(root->children.size());i+=2){
                auto* term = dynamic_cast<Term *>(root->children[i - 1]);
                if (term->token.type==TokenType::EQL){
                    res=(res==std::stof(dynamic_cast<RelExp*>(root->children[i])->v));
                }
                else if (term->token.type==TokenType::NEQ){
                    res=(res!=std::stof(dynamic_cast<RelExp*>(root->children[i])->v));
                }
                else{
                    assert(0 && "Error in eqexp!");
                }
                root->v= std::to_string(res);
                root->t=Type::IntLiteral;
            }
        }
        return;
    }
    //计算表达式结果
    root->t=dynamic_cast<RelExp*>(root->children[0])->t;
    root->v=dynamic_cast<RelExp*>(root->children[0])->v;
    if (int(root->children.size())>1){
        //确定类型
        for (int i=2;i<int(root->children.size());i+=2){
            auto relExp=dynamic_cast<RelExp*>(root->children[i]);
            auto term=dynamic_cast<Term*>(root->children[i-1]);
            Type ultimateType=root->t;
            if (root->t!=relExp->t){
                if (relExp->t==Type::Float){
                    ultimateType=Type::Float;
                }
                else if (relExp->t==Type::Int&&ultimateType==Type::IntLiteral){
                    ultimateType=Type::Int;
                }
                else if (relExp->t==Type::FloatLiteral&&ultimateType==Type::IntLiteral){
                    ultimateType=Type::FloatLiteral;
                }
                else if ((relExp->t==Type::FloatLiteral&&ultimateType==Type::Int)||(relExp->t==Type::Int&&ultimateType==Type::FloatLiteral)){
                    ultimateType=Type::Float;
                }
                //类型转换
                if (ultimateType==Type::Int){
                    if (relExp->t==Type::IntLiteral){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(relExp->v,Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Int),
                                                             ir::Operator::def));
                        relExp->v=tempName;
                        relExp->t=Type::Int;
                    }
                    if (root->t==Type::IntLiteral){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::IntLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Int),
                                                             ir::Operator::def));
                        root->v=tempName;
                        root->t=Type::Int;
                    }
                }
                else if (ultimateType==Type::FloatLiteral){
                    if (relExp->t==Type::IntLiteral){
                        relExp->v= std::to_string(std::stof(relExp->v));
                        relExp->t=Type::FloatLiteral;
                    }
                    if (root->t==Type::IntLiteral){
                        root->v= std::to_string(std::stof(root->v));
                        root->t=Type::FloatLiteral;
                    }
                }
                else if (ultimateType==Type::Float){
                    if (relExp->t==Type::IntLiteral){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(std::stof(relExp->v)),Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Float),
                                                             ir::Operator::fdef));
                        relExp->v=tempName;
                        relExp->t=Type::Float;
                    }
                    if (relExp->t==Type::Int){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(relExp->v,Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Float),
                                                             ir::Operator::cvt_i2f));
                        relExp->v=tempName;
                        relExp->t=Type::Float;
                    }
                    if (relExp->t==Type::FloatLiteral){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(relExp->v,Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Float),
                                                             ir::Operator::fdef));
                        relExp->v=tempName;
                        relExp->t=Type::Float;
                    }
                    if (root->t==Type::IntLiteral){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(std::to_string(std::stof(root->v)),Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Float),
                                                             ir::Operator::fdef));
                        root->v=tempName;
                        root->t=Type::Float;
                    }
                    if (root->t==Type::Int){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Float),
                                                             ir::Operator::cvt_i2f));
                        root->v=tempName;
                        root->t=Type::Float;
                    }
                    if (root->t==Type::FloatLiteral){
                        string tempName="t"+ std::to_string(tmp_cnt++);
                        buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::FloatLiteral),
                                                             ir::Operand(),
                                                             ir::Operand(tempName,Type::Float),
                                                             ir::Operator::fdef));
                        root->v=tempName;
                        root->t=Type::Float;
                    }
                }
            }
            //类型相同后开始计算
            if (ultimateType==Type::IntLiteral){
                if (term->token.type==TokenType::EQL){
                    root->v= std::to_string(std::stoi(root->v)== std::stoi(relExp->v));
                }
                else{
                    root->v= std::to_string(std::stoi(root->v)!= std::stoi(relExp->v));
                }
            }
            else if (ultimateType==Type::FloatLiteral){
                if (term->token.type==TokenType::EQL){
                    root->v= std::to_string(std::stof(root->v)== std::stof(relExp->v));
                }
                else{
                    root->v= std::to_string(std::stof(root->v)!= std::stof(relExp->v));
                }
            }
            else if (ultimateType==Type::Int){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                if (term->token.type==TokenType::EQL){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(relExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::eq));
                }
                else{
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Int),
                                                         ir::Operand(relExp->v,Type::Int),
                                                         ir::Operand(tempRes,Type::Int),
                                                         ir::Operator::neq));
                }
                root->v=tempRes;
                root->t=Type::Int;
            }
            else if (ultimateType==Type::Float){
                string tempRes="t"+ std::to_string(tmp_cnt++);
                if (term->token.type==TokenType::EQL){
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(relExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::feq));
                }
                else{
                    buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                         ir::Operand(relExp->v,Type::Float),
                                                         ir::Operand(tempRes,Type::Float),
                                                         ir::Operator::fneq));
                }
                root->v=tempRes;
                root->t=Type::Float;
            }
            else{
                assert(0);
            }
        }
    }
}

void frontend::Analyzer::analysisLAndExp(frontend::LAndExp* root,vector<ir::Instruction*>& buffer){
    //LAndExp -> EqExp [ '&&' LAndExp ]
    //LAndExp.is_computable
    //LAndExp.v
    //LAndExp.t

    auto* eqExp=dynamic_cast<EqExp*>(root->children[0]);
    analysisEqExp(eqExp,buffer);
    root->v=eqExp->v;
    root->t=eqExp->t;
    root->is_computable=eqExp->is_computable;
    if (int(root->children.size())>1){
        auto* lAndExp=dynamic_cast<LAndExp*>(root->children[2]);
        //考虑到短路规则，指令不一定加入
        vector<ir::Instruction*> rightInstructions;
        analysisLAndExp(lAndExp,rightInstructions);
        //常量直接计算
        if (root->is_computable&&lAndExp->is_computable){
            root->v= std::to_string(std::stof(root->v)&&(std::stof(lAndExp->v)));
            root->t=Type::IntLiteral;
            return;
        }
        //计算第1个操作数
        if (root->t==Type::Float){
            string tempLeft="t"+ std::to_string(tmp_cnt++);
            buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                 ir::Operand("0.0",Type::FloatLiteral),
                                                 ir::Operand(tempLeft,Type::Int),
                                                 ir::Operator::fneq));
            root->v=tempLeft;
            root->t=Type::Int;
        }
        else if (root->t==Type::FloatLiteral){
            root->t=Type::IntLiteral;
            root->v= std::to_string(std::stof(root->v)!=0);
        }
        //计算第2个操作数
        if (lAndExp->t==Type::Float){
            string tempRight="t"+ std::to_string(tmp_cnt++);
            rightInstructions.push_back(new ir::Instruction(ir::Operand(lAndExp->v,Type::Float),
                                                            ir::Operand("0.0",Type::FloatLiteral),
                                                            ir::Operand(tempRight,Type::Int),
                                                            ir::Operator::fneq));
            lAndExp->v=tempRight;
            lAndExp->t=Type::Int;
        }
        else if (lAndExp->t==Type::FloatLiteral){
            lAndExp->t=Type::IntLiteral;
            lAndExp->v= std::to_string(std::stof(lAndExp->v)!=0);
        }
        //计算结果
        if (root->t==Type::IntLiteral&&lAndExp->t==Type::IntLiteral){
            root->v= std::to_string(std::stoi(root->v)&& std::stoi(lAndExp->v));
        }
        else{
            string tempRes="t"+ std::to_string(tmp_cnt++);
            //真逻辑跳转
            buffer.push_back(new ir::Instruction(ir::Operand(root->v,root->t),
                                                 ir::Operand(),
                                                 ir::Operand("2",Type::IntLiteral),
                                                 ir::Operator::_goto));
            //计算右侧并赋值
            rightInstructions.push_back(new ir::Instruction(ir::Operand(root->v,root->t),
                                                            ir::Operand(lAndExp->v,lAndExp->t),
                                                            ir::Operand(tempRes,Type::Int),
                                                            ir::Operator::_and));
            //跳出假逻辑
            rightInstructions.push_back(new ir::Instruction(ir::Operand(),
                                                            ir::Operand(),
                                                            ir::Operand("2",Type::IntLiteral),
                                                            ir::Operator::_goto));
            //左侧为假直接跳出
            buffer.push_back(new ir::Instruction(ir::Operand(),
                                                 ir::Operand(),
                                                 ir::Operand(std::to_string(int(rightInstructions.size())+1),Type::IntLiteral),
                                                 ir::Operator::_goto));
            buffer.insert(buffer.end(),rightInstructions.begin(),rightInstructions.end());
            //左侧为假进行赋值
            buffer.push_back(new ir::Instruction(ir::Operand("0",Type::IntLiteral),
                                                 ir::Operand(),
                                                 ir::Operand(tempRes,Type::Int),
                                                 ir::Operator::mov));
            root->v=tempRes;
            root->t=Type::Int;
        }
    }
}

void frontend::Analyzer::analysisLOrExp(frontend::LOrExp* root,vector<ir::Instruction*>& buffer){
    //LOrExp -> LAndExp [ '||' LOrExp ]
    //LOrExp.is_computable
    //LOrExp.v
    //LOrExp.t

    auto* lAndExp=dynamic_cast<LAndExp*>(root->children[0]);
    analysisLAndExp(lAndExp,buffer);
    root->v=lAndExp->v;
    root->t=lAndExp->t;
    root->is_computable=lAndExp->is_computable;
    if (int(root->children.size())>1){
        auto* lOrExp=dynamic_cast<LOrExp*>(root->children[2]);
        //考虑到短路规则，指令不一定加入
        vector<ir::Instruction*> rightInstructions;
        analysisLOrExp(lOrExp,rightInstructions);
        //常量直接计算
        if (root->is_computable&&lAndExp->is_computable){
            root->v= std::to_string(std::stof(root->v)||(std::stof(lAndExp->v)));
            root->t=Type::IntLiteral;
            return;
        }
        //计算第1个操作数
        if (root->t==Type::Float){
            string tempLeft="t"+ std::to_string(tmp_cnt++);
            buffer.push_back(new ir::Instruction(ir::Operand(root->v,Type::Float),
                                                 ir::Operand("0.0",Type::FloatLiteral),
                                                 ir::Operand(tempLeft,Type::Int),
                                                 ir::Operator::fneq));
            root->v=tempLeft;
            root->t=Type::Int;
        }
        else if (root->t==Type::FloatLiteral){
            root->t=Type::IntLiteral;
            root->v= std::to_string(std::stof(root->v)!=0);
        }
        //计算第2个操作数
        if (lOrExp->t==Type::Float){
            string tempRight="t"+ std::to_string(tmp_cnt++);
            rightInstructions.push_back(new ir::Instruction(ir::Operand(lOrExp->v,Type::Float),
                                                 ir::Operand("0.0",Type::FloatLiteral),
                                                 ir::Operand(tempRight,Type::Int),
                                                 ir::Operator::fneq));
            lOrExp->v=tempRight;
            lOrExp->t=Type::Int;
        }
        else if (lOrExp->t==Type::FloatLiteral){
            lOrExp->t=Type::IntLiteral;
            lOrExp->v= std::to_string(std::stof(lOrExp->v)!=0);
        }
        //计算结果
        if (root->t==Type::IntLiteral&&lOrExp->t==Type::IntLiteral){
            root->v= std::to_string(std::stoi(root->v)|| std::stoi(lOrExp->v));
        }
        else{
            string tempRes="t"+ std::to_string(tmp_cnt++);
            //假逻辑指令
            rightInstructions.push_back(new ir::Instruction(ir::Operand(root->v,root->t),
                                                            ir::Operand(lOrExp->v,lOrExp->t),
                                                            ir::Operand(tempRes,ir::Type::Int),
                                                            ir::Operator::_or));
            //真逻辑跳转
            buffer.push_back(new ir::Instruction(ir::Operand(root->v,root->t),
                                                 ir::Operand(),
                                                 ir::Operand("2",Type::IntLiteral),
                                                 ir::Operator::_goto));
            //假逻辑跳转
            buffer.push_back(new ir::Instruction(ir::Operand(),
                                                 ir::Operand(),
                                                 ir::Operand("3",Type::IntLiteral),
                                                 ir::Operator::_goto));
            //真逻辑赋值
            buffer.push_back(new ir::Instruction(ir::Operand("1",Type::IntLiteral),
                                                 ir::Operand(),
                                                 ir::Operand(tempRes,ir::Type::Int),
                                                 ir::Operator::mov));
            //真逻辑跳转
            buffer.push_back(new ir::Instruction(ir::Operand(),
                                                 ir::Operand(),
                                                 ir::Operand(std::to_string(int(rightInstructions.size())+1),Type::IntLiteral),
                                                 ir::Operator::_goto));
            buffer.insert(buffer.end(),rightInstructions.begin(),rightInstructions.end());
            root->v=tempRes;
            root->t=Type::Int;
        }
    }
}

void frontend::Analyzer::analysisConstExp(frontend::ConstExp* root,vector<ir::Instruction*>& buffer){
    //ConstExp -> AddExp
    //ConstExp.is_computable: true
    //ConstExp.v
    //ConstExp.t

    auto addExp=dynamic_cast<AddExp*>(root->children[0]);
    analysisAddExp(addExp,buffer);
    assert(addExp->t==Type::IntLiteral||addExp->t==Type::FloatLiteral);
    root->v=addExp->v;
    root->t=addExp->t;
}