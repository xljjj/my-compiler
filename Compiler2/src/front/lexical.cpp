#include"front/lexical.h"

#include<map>
#include<cassert>
#include<string>
#include <sstream>

#define TODO assert(0 && "todo")

// #define DEBUG_DFA
// #define DEBUG_SCANNER

std::string frontend::toString(State s) {
    switch (s) {
        case State::Empty: return "Empty";
        case State::Ident: return "Ident";
        case State::IntLiteral: return "IntLiteral";
        case State::FloatLiteral: return "FloatLiteral";
        case State::op: return "op";
        case State::Comment: return "Comment";
        default:
            assert(0 && "invalid State");
    }
    return "";
}

std::set<std::string> frontend::keywords= {
        "const", "int", "float", "if", "else", "while", "continue", "break", "return", "void"
};

frontend::TokenType stateToTokenType(frontend::State& s,std::string& value){
    //int值
    if (s==frontend::State::IntLiteral){
        return frontend::TokenType::INTLTR;
    }
        //float值
    else if (s==frontend::State::FloatLiteral){
        return frontend::TokenType::FLOATLTR;
    }
        //符号
    else if (s==frontend::State::op){
        if (value=="+"){
            return frontend::TokenType::PLUS;
        }
        else if (value=="-"){
            return frontend::TokenType::MINU;
        }
        else if (value=="*"){
            return frontend::TokenType::MULT;
        }
        else if (value=="/"){
            return frontend::TokenType::DIV;
        }
        else if (value=="%"){
            return frontend::TokenType::MOD;
        }
        else if (value=="<"){
            return frontend::TokenType::LSS;
        }
        else if (value==">"){
            return frontend::TokenType::GTR;
        }
        else if (value==":"){
            return frontend::TokenType::COLON;
        }
        else if (value=="="){
            return frontend::TokenType::ASSIGN;
        }
        else if (value==";"){
            return frontend::TokenType::SEMICN;
        }
        else if (value==","){
            return frontend::TokenType::COMMA;
        }
        else if (value=="("){
            return frontend::TokenType::LPARENT;
        }
        else if (value==")"){
            return frontend::TokenType::RPARENT;
        }
        else if (value=="["){
            return frontend::TokenType::LBRACK;
        }
        else if (value=="]"){
            return frontend::TokenType::RBRACK;
        }
        else if (value=="{"){
            return frontend::TokenType::LBRACE;
        }
        else if (value=="}"){
            return frontend::TokenType::RBRACE;
        }
        else if (value=="!"){
            return frontend::TokenType::NOT;
        }
        else if (value=="<="){
            return frontend::TokenType::LEQ;
        }
        else if (value==">="){
            return frontend::TokenType::GEQ;
        }
        else if (value=="=="){
            return frontend::TokenType::EQL;
        }
        else if (value=="!="){
            return frontend::TokenType::NEQ;
        }
        else if (value=="&&"){
            return frontend::TokenType::AND;
        }
        else{
            return frontend::TokenType::OR;
        }
    }
        //标识符
    else{
        if (value=="const"){
            return frontend::TokenType::CONSTTK;
        }
        else if (value=="void"){
            return frontend::TokenType::VOIDTK;
        }
        else if (value=="int"){
            return frontend::TokenType::INTTK;
        }
        else if (value=="float"){
            return frontend::TokenType::FLOATTK;
        }
        else if (value=="if"){
            return frontend::TokenType::IFTK;
        }
        else if (value=="else"){
            return frontend::TokenType::ELSETK;
        }
        else if (value=="while"){
            return frontend::TokenType::WHILETK;
        }
        else if (value=="continue"){
            return frontend::TokenType::CONTINUETK;
        }
        else if (value=="break"){
            return frontend::TokenType::BREAKTK;
        }
        else if (value=="return"){
            return frontend::TokenType::RETURNTK;
        }
        else{
            return frontend::TokenType::IDENFR;
        }
    }
}

frontend::DFA::DFA(): cur_state(frontend::State::Empty), cur_str() {}

frontend::DFA::~DFA() {}

bool frontend::DFA::next(char input, Token& buf) {
#ifdef DEBUG_DFA
    #include<iostream>
    std::cout << "in state [" << toString(cur_state) << "], input = \'" << input << "\', str = " << cur_str << "\t";
#endif
    //注释状态
    if (cur_state==State::Comment){
        if (cur_str=="//"){
            if (input=='\n'||input=='\r'){
                cur_str="";
                cur_state=State::Empty;
            }
        }
        else{
            if (input=='*'){
                cur_str='*';
            }
            else if (cur_str=="*"&&input=='/'){
                cur_str="";
                cur_state=State::Empty;
            }
            else{
                cur_str="";
            }
        }
        return false;
    }
    //输入为间隔
    if (input==' '||input=='\t'||input=='\n'||input=='\r'){
        if (cur_state==State::Empty){
            return false;
        }
        else{
            buf.type=stateToTokenType(cur_state,cur_str);
            buf.value=cur_str;
            cur_state=State::Empty;
            cur_str="";
            return true;
        }
    }
        //输入为数字
    else if (input>='0'&&input<='9'){
        if (cur_state==State::Empty){
            cur_state=State::IntLiteral;
            cur_str=input;
            return false;
        }
        else if (cur_state==State::op){
            buf.type=stateToTokenType(cur_state,cur_str);
            buf.value=cur_str;
            cur_state=State::IntLiteral;
            cur_str=input;
            return true;
        }
        else{
            cur_str+=input;
            return false;
        }
    }
        //输入为点
    else if (input=='.'){
        if (cur_state==State::IntLiteral){
            cur_state=State::FloatLiteral;
            cur_str+=input;
            return false;
        }
            //其他
        else{
            buf.type=stateToTokenType(cur_state,cur_str);
            buf.value=cur_str;
            cur_state=State::FloatLiteral;
            cur_str=input;
            return true;
        }
    }
        //输入为字母或下划线
    else if ((input>='a'&&input<='z')||(input>='A'&&input<='Z')||input=='_'){
        if (cur_state==State::Empty){
            cur_state=State::Ident;
            cur_str+=input;
            return false;
        }
        else if (cur_state==State::Ident||cur_state==State::IntLiteral){
            cur_str+=input;
            return false;
        }
        else if (cur_state==State::op){
            buf.type=stateToTokenType(cur_state,cur_str);
            buf.value=cur_str;
            cur_state=State::Ident;
            cur_str=input;
            return true;
        }
            //错误
        else{
            return false;
        }
    }
        //输入为符号
    else{
        if (cur_state==State::Empty){
            cur_state=State::op;
            cur_str=input;
            return false;
        }
        else if (cur_state==State::op){
            if ((cur_str=="<"&&input=='=')||(cur_str==">"&&input=='=')||(cur_str=="="&&input=='=')
                ||(cur_str=="!"&&input=='=')||(cur_str=="&"&&input=='&')||(cur_str=="|"&&input=='|')){
                cur_str+=input;
                return false;
            }
            else if (cur_str=="/"&&input=='/'){
                cur_state=State::Comment;
                cur_str="//";
                return false;
            }
            else if (cur_str=="/"&&input=='*'){
                cur_state=State::Comment;
                cur_str="";
                return false;
            }
            else{
                buf.type=stateToTokenType(cur_state,cur_str);
                buf.value=cur_str;
                cur_str=input;
                return true;
            }
        }
        else{
            buf.type=stateToTokenType(cur_state,cur_str);
            buf.value=cur_str;
            cur_state=State::op;
            cur_str=input;
            return true;
        }
    }
#ifdef DEBUG_DFA
    std::cout << "next state is [" << toString(cur_state) << "], next str = " << cur_str << "\t, ret = " << ret << std::endl;
#endif
}

void frontend::DFA::reset() {
    cur_state = State::Empty;
    cur_str = "";
}

frontend::Scanner::Scanner(std::string filename): fin(filename) {
    if(!fin.is_open()) {
        assert(0 && "in Scanner constructor, input file cannot open");
    }
}

frontend::Scanner::~Scanner() {
    fin.close();
}

std::vector<frontend::Token> frontend::Scanner::run() {
    std::vector<Token> res;
    Token tk;
    DFA dfa;
    //将文件流转化为字符串
    std::stringstream strStream;
    strStream<<fin.rdbuf();
    std::string s=strStream.str();
    s+='\n';
    for (auto& c:s){
        if (dfa.next(c,tk)){
            res.push_back(tk);
        }
    }
#ifdef DEBUG_SCANNER
    #include<iostream>
            std::cout << "token: " << toString(tk.type) << "\t" << tk.value << std::endl;
#endif
    return res;
}