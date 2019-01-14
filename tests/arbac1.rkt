#lang emcsarbac

policy original
  permit if: admin s, read a, file r.    
end;

policy mod1
  permit if: admin s, read a, file r.   
  permit if: accountant s, read a, under-audit r.
end;

compare original mod1;
//test original admin s, read a, under-audit r;
//test original not admin s, read a, under-audit r;
//test mod1     not admin s, read a, under-audit r;