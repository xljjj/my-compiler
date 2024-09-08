#include"front/syntax.h"

#include<iostream>
#include<cassert>

using frontend::Parser;

// #define DEBUG_PARSER
#define TODO assert(0 && "todo")
#define CUR_TOKEN_IS(tk_type) (token_stream[index].type == TokenType::tk_type)
#define PARSE_TOKEN(tk_type) root->children.push_back(parseTerm(root, TokenType::tk_type))
#define PARSE(name, type) auto name = new type(root); assert(parse##type(name)); root->children.push_back(name);


Parser::Parser(const std::vector<frontend::Token>& tokens): index(0), token_stream(tokens) {}

Parser::~Parser() {}

frontend::CompUnit* Parser::get_abstract_syntax_tree(){
    auto* root=new CompUnit();
    parseCompUnit(root);
    return root;
}

frontend::Term* Parser::parseTerm(frontend::AstNode* parent,frontend::TokenType expected){
    if (token_stream[index].type==expected){
        Token t;
        t.type=expected;
        t.value=token_stream[index].value;
        auto son=new Term(t,parent);
        index++;
        return son;
    }
    else{
        std::cout<<"Required Type: "<<toString(expected)<<std::endl;
        std::cout<<"Cur Type: "<<toString(token_stream[index].type)<<std::endl;
        assert(0);
        return nullptr;
    }
}

bool Parser::parseCompUnit(frontend::CompUnit* root){
    //CompUnit -> (Decl | FuncDef) [CompUnit]

    if (CUR_TOKEN_IS(CONSTTK)){
        PARSE(decl,Decl);
    }
    else if(CUR_TOKEN_IS(VOIDTK)){
        PARSE(funcDef,FuncDef);
    }
    else if(CUR_TOKEN_IS(INTTK)|| CUR_TOKEN_IS(FLOATTK)){
        if (token_stream[index+2].type==TokenType::LPARENT){
            PARSE(funcDef,FuncDef);
        }
        else{
            PARSE(decl,Decl);
        }
    }
    else{
        assert(0);
    }
    if (index<token_stream.size()){
        PARSE(compUnit,CompUnit);
    }

    return true;
}

bool Parser::parseDecl(frontend::Decl* root){
    //Decl -> ConstDecl | VarDecl

    if (CUR_TOKEN_IS(CONSTTK)){
        PARSE(constDecl,ConstDecl);
    }
    else if (CUR_TOKEN_IS(INTTK)|| CUR_TOKEN_IS(FLOATTK)){
        PARSE(varDecl,VarDecl);
    }
    else{
        assert(0);
    }

    return true;
}

bool Parser::parseFuncDef(frontend::FuncDef* root){
    //FuncDef -> FuncType Ident '(' [FuncFParams] ')' Block

    PARSE(functype, FuncType);
    PARSE_TOKEN(IDENFR);
    PARSE_TOKEN(LPARENT);

    // no [FuncFParams], FuncType Ident '(' ')' Block
    if(CUR_TOKEN_IS(RPARENT)) {
        PARSE_TOKEN(RPARENT);
    }
        // FuncType Ident '(' FuncFParams ')' Block
    else {
        PARSE(node, FuncFParams);
        PARSE_TOKEN(RPARENT);
    }

    PARSE(block, Block);
    return true;
}

bool Parser::parseConstDecl(frontend::ConstDecl* root){
    //ConstDecl -> 'const' BType ConstDef { ',' ConstDef } ';'

    PARSE_TOKEN(CONSTTK);
    PARSE(bType,BType);
    PARSE(constDef,ConstDef);
    while (!CUR_TOKEN_IS(SEMICN)){
        PARSE_TOKEN(COMMA);
        PARSE(constDefTemp,ConstDef);
    }
    PARSE_TOKEN(SEMICN);

    return true;
}

bool Parser::parseBType(frontend::BType* root){
    //BType -> 'int' | 'float'

    if (CUR_TOKEN_IS(INTTK)){
        PARSE_TOKEN(INTTK);
    }
    else if (CUR_TOKEN_IS(FLOATTK)){
        PARSE_TOKEN(FLOATTK);
    }
    else{
        assert(0);
    }

    return true;
}

bool Parser::parseConstDef(frontend::ConstDef* root){
    //ConstDef -> Ident { '[' ConstExp ']' } '=' ConstInitVal

    PARSE_TOKEN(IDENFR);
    while (!CUR_TOKEN_IS(ASSIGN)){
        PARSE_TOKEN(LBRACK);
        PARSE(constExp,ConstExp);
        PARSE_TOKEN(RBRACK);
    }
    PARSE_TOKEN(ASSIGN);
    PARSE(constInitVal,ConstInitVal);

    return true;
}

bool Parser::parseConstInitVal(frontend::ConstInitVal* root){
    //ConstInitVal -> ConstExp | '{' [ ConstInitVal { ',' ConstInitVal } ] '}'
    if (CUR_TOKEN_IS(LBRACE)){
        PARSE_TOKEN(LBRACE);
        if (!CUR_TOKEN_IS(RBRACE)){
            PARSE(constInitVal,ConstInitVal);
            while (CUR_TOKEN_IS(COMMA)){
                PARSE_TOKEN(COMMA);
                PARSE(constInitValTemp,ConstInitVal);
            }
        }
        PARSE_TOKEN(RBRACE);
    }
    else{
        PARSE(constExp,ConstExp);
    }

    return true;
}

bool Parser::parseVarDecl(frontend::VarDecl* root){
    //VarDecl -> BType VarDef { ',' VarDef } ';'

    PARSE(bType,BType);
    PARSE(varDef,VarDef);
    while (!CUR_TOKEN_IS(SEMICN)){
        PARSE_TOKEN(COMMA);
        PARSE(varDefTemp,VarDef);
    }
    PARSE_TOKEN(SEMICN);

    return true;
}

bool Parser::parseVarDef(frontend::VarDef* root){
    //VarDef -> Ident { '[' ConstExp ']' } [ '=' InitVal ]

    PARSE_TOKEN(IDENFR);
    while (CUR_TOKEN_IS(LBRACK)){
        PARSE_TOKEN(LBRACK);
        PARSE(constExp,ConstExp);
        PARSE_TOKEN(RBRACK);
    }
    if (CUR_TOKEN_IS(ASSIGN)){
        PARSE_TOKEN(ASSIGN);
        PARSE(initVal,InitVal);
    }

    return true;
}

bool Parser::parseInitVal(frontend::InitVal* root){
    //InitVal -> Exp | '{' [ InitVal { ',' InitVal } ] '}'

    if (CUR_TOKEN_IS(LBRACE)){
        PARSE_TOKEN(LBRACE);
        if (!CUR_TOKEN_IS(RBRACE)){
            PARSE(initVal,InitVal);
            while (CUR_TOKEN_IS(COMMA)){
                PARSE_TOKEN(COMMA);
                PARSE(initValTemp,InitVal);
            }
        }
        PARSE_TOKEN(RBRACE);
    }
    else{
        PARSE(exp,Exp);
    }

    return true;
}

bool Parser::parseFuncType(frontend::FuncType* root){
    //FuncType -> 'void' | 'int' | 'float'

    if (CUR_TOKEN_IS(VOIDTK)){
        PARSE_TOKEN(VOIDTK);
    }
    else if (CUR_TOKEN_IS(INTTK)){
        PARSE_TOKEN(INTTK);
    }
    else if (CUR_TOKEN_IS(FLOATTK)){
        PARSE_TOKEN(FLOATTK);
    }
    else{
        assert(0);
    }

    return true;
}

bool Parser::parseFuncFParam(frontend::FuncFParam* root){
    //FuncFParam -> BType Ident ['[' ']' { '[' Exp ']' }]

    PARSE(bType,BType);
    PARSE_TOKEN(IDENFR);
    if (CUR_TOKEN_IS(LBRACK)){
        PARSE_TOKEN(LBRACK);
        PARSE_TOKEN(RBRACK);
        while (CUR_TOKEN_IS(LBRACK)){
            PARSE_TOKEN(LBRACK);
            PARSE(exp,Exp);
            PARSE_TOKEN(RBRACK);
        }
    }

    return true;
}

bool Parser::parseFuncFParams(frontend::FuncFParams* root){
    //FuncFParams -> FuncFParam { ',' FuncFParam }

    PARSE(funcFParam,FuncFParam);
    while (CUR_TOKEN_IS(COMMA)){
        PARSE_TOKEN(COMMA);
        PARSE(funcFParamTemp,FuncFParam);
    }

    return true;
}

bool Parser::parseBlock(frontend::Block* root){
    //Block -> '{' { BlockItem } '}'

    PARSE_TOKEN(LBRACE);
    while (!CUR_TOKEN_IS(RBRACE)){
        PARSE(blockItem,BlockItem);
    }
    PARSE_TOKEN(RBRACE);

    return true;
}

bool Parser::parseBlockItem(frontend::BlockItem* root){
    //BlockItem -> Decl | Stmt

    if (CUR_TOKEN_IS(CONSTTK)|| CUR_TOKEN_IS(INTTK)|| CUR_TOKEN_IS(FLOATTK)){
        PARSE(decl,Decl);
    }
    else{
        PARSE(stmt,Stmt);
    }

    return true;
}

bool Parser::parseStmt(frontend::Stmt* root){
    //Stmt -> LVal '=' Exp ';' | Block | 'if' '(' Cond ')' Stmt [ 'else' Stmt ] |
    //'while' '(' Cond ')' Stmt | 'break' ';' | 'continue' ';' | 'return' [Exp] ';' | [Exp] ';'

    if (CUR_TOKEN_IS(IDENFR)){
        if (token_stream[index+1].type==TokenType::LPARENT){
            PARSE(exp,Exp);
            PARSE_TOKEN(SEMICN);
        }
        else{
            PARSE(lVal,LVal);
            PARSE_TOKEN(ASSIGN);
            PARSE(exp,Exp);
            PARSE_TOKEN(SEMICN);
        }
    }
    else if (CUR_TOKEN_IS(LBRACE)){
        PARSE(block,Block);
    }
    else if (CUR_TOKEN_IS(IFTK)){
        PARSE_TOKEN(IFTK);
        PARSE_TOKEN(LPARENT);
        PARSE(cond,Cond);
        PARSE_TOKEN(RPARENT);
        PARSE(stmt,Stmt);
        if (CUR_TOKEN_IS(ELSETK)){
            PARSE_TOKEN(ELSETK);
            PARSE(stmtTemp,Stmt);
        }
    }
    else if (CUR_TOKEN_IS(WHILETK)){
        PARSE_TOKEN(WHILETK);
        PARSE_TOKEN(LPARENT);
        PARSE(cond,Cond);
        PARSE_TOKEN(RPARENT);
        PARSE(stmt,Stmt);
    }
    else if (CUR_TOKEN_IS(BREAKTK)){
        PARSE_TOKEN(BREAKTK);
        PARSE_TOKEN(SEMICN);
    }
    else if (CUR_TOKEN_IS(CONTINUETK)){
        PARSE_TOKEN(CONTINUETK);
        PARSE_TOKEN(SEMICN);
    }
    else if (CUR_TOKEN_IS(RETURNTK)){
        PARSE_TOKEN(RETURNTK);
        if (!CUR_TOKEN_IS(SEMICN)){
            PARSE(exp,Exp);
        }
        PARSE_TOKEN(SEMICN);
    }
    else{
        if (!CUR_TOKEN_IS(SEMICN)){
            PARSE(exp,Exp);
        }
        PARSE_TOKEN(SEMICN);
    }

    return true;
}

bool Parser::parseExp(frontend::Exp* root){
    //Exp -> AddExp

    PARSE(addExp,AddExp);

    return true;
}

bool Parser::parseCond(frontend::Cond* root){
    //Cond -> LOrExp

    PARSE(lOrExp,LOrExp);

    return true;
}

bool Parser::parseLVal(frontend::LVal* root){
    //LVal -> Ident {'[' Exp ']'}

    PARSE_TOKEN(IDENFR);
    while (CUR_TOKEN_IS(LBRACK)){
        PARSE_TOKEN(LBRACK);
        PARSE(exp,Exp);
        PARSE_TOKEN(RBRACK);
    }

    return true;
}

bool Parser::parseNumber(frontend::Number* root){
    //Number -> IntConst | floatConst

    if (CUR_TOKEN_IS(INTLTR)){
        PARSE_TOKEN(INTLTR);
    }
    else if (CUR_TOKEN_IS(FLOATLTR)){
        PARSE_TOKEN(FLOATLTR);
    }
    else{
        assert(0);
    }

    return true;
}

bool Parser::parsePrimaryExp(frontend::PrimaryExp* root){
    // PrimaryExp -> '(' Exp ')' | LVal | Number

    if (CUR_TOKEN_IS(LPARENT)){
        PARSE_TOKEN(LPARENT);
        PARSE(exp,Exp);
        PARSE_TOKEN(RPARENT);
    }
    else if (CUR_TOKEN_IS(IDENFR)){
        PARSE(lVal,LVal);
    }
    else if (CUR_TOKEN_IS(INTLTR)|| CUR_TOKEN_IS(FLOATLTR)){
        PARSE(number,Number);
    }
    else{
        assert(0);
    }

    return true;
}

bool Parser::parseUnaryExp(frontend::UnaryExp* root){
    //UnaryExp -> PrimaryExp | Ident '(' [FuncRParams] ')' | UnaryOp UnaryExp

    if (CUR_TOKEN_IS(PLUS)|| CUR_TOKEN_IS(MINU)|| CUR_TOKEN_IS(NOT)){
        PARSE(unaryOp,UnaryOp);
        PARSE(unaryExp,UnaryExp);
    }
    else if (CUR_TOKEN_IS(IDENFR)&&token_stream[index+1].type==TokenType::LPARENT){
        PARSE_TOKEN(IDENFR);
        PARSE_TOKEN(LPARENT);
        if (!CUR_TOKEN_IS(RPARENT)){
            PARSE(funcRParams,FuncRParams);
        }
        PARSE_TOKEN(RPARENT);
    }
    else{
        PARSE(primaryExp,PrimaryExp);
    }

    return true;
}

bool Parser::parseUnaryOp(frontend::UnaryOp* root){
    //UnaryOp -> '+' | '-' | '!'

    if (CUR_TOKEN_IS(PLUS)){
        PARSE_TOKEN(PLUS);
    }
    else if (CUR_TOKEN_IS(MINU)){
        PARSE_TOKEN(MINU);
    }
    else if (CUR_TOKEN_IS(NOT)){
        PARSE_TOKEN(NOT);
    }
    else{
        assert(0);
    }

    return true;
}

bool Parser::parseFuncRParams(frontend::FuncRParams* root){
    //FuncRParams -> Exp { ',' Exp }

    PARSE(exp,Exp);
    while (CUR_TOKEN_IS(COMMA)){
        PARSE_TOKEN(COMMA);
        PARSE(expTemp,Exp);
    }

    return true;
}

bool Parser::parseMulExp(frontend::MulExp* root){
    //MulExp -> UnaryExp { ('*' | '/' | '%') UnaryExp }

    PARSE(unaryExp,UnaryExp);
    while (CUR_TOKEN_IS(MULT)|| CUR_TOKEN_IS(DIV)|| CUR_TOKEN_IS(MOD)){
        if (CUR_TOKEN_IS(MULT)){
            PARSE_TOKEN(MULT);
        }
        else if (CUR_TOKEN_IS(DIV)){
            PARSE_TOKEN(DIV);
        }
        else{
            PARSE_TOKEN(MOD);
        }
        PARSE(unaryExpTemp,UnaryExp);
    }

    return true;
}

bool Parser::parseAddExp(frontend::AddExp* root){
    //AddExp -> MulExp { ('+' | '-') MulExp }

    PARSE(mulExp,MulExp);
    while (CUR_TOKEN_IS(PLUS)|| CUR_TOKEN_IS(MINU)){
        if (CUR_TOKEN_IS(PLUS)){
            PARSE_TOKEN(PLUS);
        }
        else{
            PARSE_TOKEN(MINU);
        }
        PARSE(mulExpTemp,MulExp);
    }

    return true;
}

bool Parser::parseRelExp(frontend::RelExp* root){
    //RelExp -> AddExp { ('<' | '>' | '<=' | '>=') AddExp }

    PARSE(addExp,AddExp);
    while (CUR_TOKEN_IS(LSS)|| CUR_TOKEN_IS(GTR)|| CUR_TOKEN_IS(LEQ)|| CUR_TOKEN_IS(GEQ)){
        if (CUR_TOKEN_IS(LSS)){
            PARSE_TOKEN(LSS);
        }
        else if (CUR_TOKEN_IS(GTR)){
            PARSE_TOKEN(GTR);
        }
        else if (CUR_TOKEN_IS(LEQ)){
            PARSE_TOKEN(LEQ);
        }
        else{
            PARSE_TOKEN(GEQ);
        }
        PARSE(addExpTemp,AddExp);
    }

    return true;
}

bool Parser::parseEqExp(frontend::EqExp* root){
    //EqExp -> RelExp { ('==' | '!=') RelExp }

    PARSE(relExp,RelExp);
    while (CUR_TOKEN_IS(EQL)|| CUR_TOKEN_IS(NEQ)){
        if (CUR_TOKEN_IS(EQL)){
            PARSE_TOKEN(EQL);
        }
        else{
            PARSE_TOKEN(NEQ);
        }
        PARSE(relExpTemp,RelExp);
    }

    return true;
}

bool Parser::parseLAndExp(frontend::LAndExp* root){
    //LAndExp -> EqExp [ '&&' LAndExp ]

    PARSE(eqexp,EqExp);
    if (CUR_TOKEN_IS(AND)){
        PARSE_TOKEN(AND);
        PARSE(lAndExp,LAndExp);
    }

    return true;
}

bool Parser::parseLOrExp(frontend::LOrExp* root){
    //LOrExp -> LAndExp [ '||' LOrExp ]

    PARSE(lAndExp,LAndExp);
    if (CUR_TOKEN_IS(OR)){
        PARSE_TOKEN(OR);
        PARSE(lOrExp,LOrExp);
    }

    return true;
}

bool Parser::parseConstExp(frontend::ConstExp* root){
    //ConstExp -> AddExp

    PARSE(addExp,AddExp);

    return true;
}

void Parser::log(AstNode* node){
#ifdef DEBUG_PARSER
    std::cout << "in parse" << toString(node->type) << ", cur_token_type::" << toString(token_stream[index].type) << ", token_val::" << token_stream[index].value << '\n';
#endif
}

