grammar HLL;

Term : AppTerm
     | LAMBDA LIDENT DOT Term;

AppTerm : ATerm
        | AppTerm ATerm;

/* Atomic terms are ones that never require extra parentheses */
ATerm : LPAREN Term RPAREN
      | Var
      | Fun;

Var: LIDENT;
Fun: '&' LIDENT;


LAMBDA : '\\' ;
DOT    : '.' ;
LIDENT : [a-z][a-zA-Z0-9]* ;
UIDENT : [a-z][a-zA-Z0-9]* ;
LPAREN : '(' ;
RPAREN : ')' ;


prog:	(expr NEWLINE)* ;
expr:	expr ('*'|'/') expr
    |	expr ('+'|'-') expr
    |	INT
    |	'(' expr ')'
    ;
NEWLINE : [\r\n]+ ;
INT     : [0-9]+ ;