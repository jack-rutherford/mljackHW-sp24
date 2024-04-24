structure jack =
struct
open jackAS;
    
     structure jackLrVals = jackLrValsFun(structure Token = LrParser.Token) 
               
     structure jackLex = jackLexFun(structure Tokens = jackLrVals.Tokens)

     structure jackParser = Join(structure Lex= jackLex
                                structure LrParser = LrParser
                                structure ParserData = jackLrVals.ParserData)
                                  
     val input_line =
       fn f =>
          let val sOption = TextIO.inputLine f
          in
            if isSome(sOption) then
               Option.valOf(sOption)
            else
               ""
          end

     val jackparse = 
         fn filename =>
           let val instrm = TextIO.openIn filename
               val lexer = jackParser.makeLexer(fn i => input_line instrm)
               val _ = jackLex.UserDeclarations.pos := 1
               val error = fn (e,i:int,_) => 
                               TextIO.output(TextIO.stdOut," line " ^ (Int.toString i) ^ ", Error: " ^ e ^ "\n")
           in 
                jackParser.parse(30,lexer,error,()) before TextIO.closeIn instrm
           end

     (* These functions are needed for if-then-else expressions and functions *)
     val label = ref 0;

     fun nextLabel() = 
         let val lab = !label
         in 
           label := !label + 1;
           "L"^Int.toString(lab)
         end

     (* a binding is a 4-tuple of (name, typ, segment, offset) *)
     exception unboundId;  
     
     (* find the type, segment and offset for an identifier *)
     fun boundTo(name:string,[]) = 
         (TextIO.output(TextIO.stdOut, "Unbound identifier "^name^" referenced!\n");
          raise unboundId)
       | boundTo(name,(n,typ,segment,offset)::t) = if name=n then (typ,segment,offset) else boundTo(name,t);

    
     fun checkBoundTo(name:string,[]) = 
         (false)
       | checkBoundTo(name,(n,typ,segment,offset)::t) = if name=n then true else checkBoundTo(name,t);

     (* create a list of bindings from a list of names in a particular segment *)
	 fun createBindings([],typ,segment,offset) = []
	   | createBindings(name::names,typ,segment,offset) = (TextIO.output(TextIO.stdOut,"generating binding for "^name^":"^typ^":"^segment^":"^Int.toString(offset)^"\n");
							       (name,typ,segment,offset)::createBindings(names,typ,segment,offset+1))

     (* create a list of bindings from class variables; sort them into static and field segments *)
     fun createClassBindings(cvList) = 
	 let fun ccbHelper([],soffset,foffset) = []
	       | ccbHelper((seg,typ,names)::t,soffset,foffset) =
		 if seg = "static" then
		     createBindings(names,typ,"static",soffset)@ccbHelper(t,soffset+length(names),foffset)
		 else
		     createBindings(names,typ,"this",foffset)@ccbHelper(t,soffset,foffset+length(names))
	 in
	     ccbHelper(cvList,0,0)
	 end

     (* create a list of bindings from parameters; each param is a (type,name) tuple *)
     fun createParamBindings([],offset) = []
       | createParamBindings((typ,name)::t,offset) = 
	 createBindings([name],typ,"argument",offset)@createParamBindings(t,offset+1)

     (* create a list of bindings from local variable declarations *)
     fun createLocalBindings(vardecs) =
	 let fun createLocalBindingsHelper([],offset) = []
	       | createLocalBindingsHelper((typ,names)::t,offset) = 
		 createBindings(names,typ,"local",offset)@createLocalBindingsHelper(t,offset+length(names))
	 in
	     createLocalBindingsHelper(vardecs,0)
	 end

     (* find the number of bindings in a particular segment *)
     fun numBindings(seg,[]) = 0
       | numBindings(seg,(_,_,bseg,_)::t) = (if seg = bseg then 1 else 0) + numBindings(seg,t)

     (* This is the code generation for the compiler *)

     exception Unimplemented; 
  
     (* codegen takes an AST node, the output file, a list of bindings, and the class name *)
     fun codegen(class'(id,classVars,subroutines),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to compile class named "^id^"\n");
        let val bindingsNew = createClassBindings(classVars)
        in
          codegenlist(subroutines,outFile,(bindingsNew@bindings),id)
        end
      )

    | codegen(constructor'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to compile constructor named "^id^"\n");
        (* TextIO.output(TextIO.stdOut, "Number of local variables: "^Int.toString(length vardecs)^"\n"); *)
        let val paramBindings = createParamBindings(params, 0)
            val localBindings = createLocalBindings(vardecs)
            val bindingsNew = paramBindings@localBindings@bindings
        in
          (* TextIO.output(TextIO.stdOut, "Number of param bindings: "^Int.toString(length paramBindings)^"\n");
          TextIO.output(TextIO.stdOut, "Number of local bindings: "^Int.toString(length localBindings)^"\n");
          TextIO.output(TextIO.stdOut, "Number of bindingsNew: "^Int.toString(length bindingsNew)^"\n"); *)
          TextIO.output(outFile,"function "^className^"."^id^" "^Int.toString(length vardecs)^"\n");
          TextIO.output(outFile,"push constant "^(Int.toString(numBindings("this", bindingsNew)))^"\n");
          TextIO.output(outFile,"call Memory.alloc 1\n");
          TextIO.output(outFile,"pop pointer 0\n");
          codegenlist(statements,outFile,(paramBindings@localBindings@bindings),className)
        end
      )

    | codegen(function'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
	    (
        TextIO.output(TextIO.stdOut, "Attempt to compile function named "^id^"\n");
        let val paramBindings = createParamBindings(params, 0)
            val localBindings = createLocalBindings(vardecs)
            val bindingsNew = paramBindings@localBindings@bindings
        in
          TextIO.output(outFile,"function "^className^"."^id^" "^Int.toString(length vardecs)^"\n");
          codegenlist(statements,outFile,(paramBindings@localBindings@bindings),className)
        end
      )

    | codegen(method'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
        (
          TextIO.output(TextIO.stdOut, "Attempt to compile method named "^id^"\n");
          let val paramBindings = createParamBindings(params, 1)
              val localBindings = createLocalBindings(vardecs)
              val bindingsNew = paramBindings@localBindings@bindings
          in
            (* TextIO.output(TextIO.stdOut, "Number of local variables: "^Int.toString(length vardecs)^"\n");
            TextIO.output(TextIO.stdOut, "Number of local bindings: "^Int.toString(length localBindings)^"\n");
            TextIO.output(TextIO.stdOut, "Number of param bindings: "^Int.toString(length paramBindings)^"\n");
            TextIO.output(TextIO.stdOut, "Number of bindings: "^Int.toString(length bindings)^"\n");
            TextIO.output(TextIO.stdOut, "Number of bindingsNew: "^Int.toString(length bindingsNew)^"\n"); *)
            TextIO.output(outFile,"function "^className^"."^id^" "^Int.toString(length localBindings)^"\n");
            TextIO.output(outFile,"push argument 0\npop pointer 0\n");
            codegenlist(statements,outFile,bindingsNew,className)
          end
        )

    | codegen(letval'(id,e),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to compile letval\n");
        let val (typ,segment,offset) = boundTo(id,bindings)
        in
          codegen(e,outFile,bindings,className);
          TextIO.output(outFile, "pop "^segment^" "^Int.toString(offset)^"\n")
        end
      )

    | codegen(letarray'(id,e1,e2),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to compile letarray\n");
        let val (typ,segment,offset) = boundTo(id,bindings)
        in
          codegen(e1,outFile,bindings,className);
          TextIO.output(outFile, "push "^segment^" "^Int.toString(offset)^"\n");
          TextIO.output(outFile, "add\n");
          codegen(e2,outFile,bindings,className);
          TextIO.output(outFile, "pop temp 0\npop pointer 1\npush temp 0\npop that 0\n")
        end
      )

    | codegen(if'(e,stmt),outFile,bindings,className) =
        (
          TextIO.output(TextIO.stdOut, "Attempt to compile if statement\n");
          let val l1 = nextLabel()
              val l2 = nextLabel()
          in
            codegen(e,outFile,bindings,className);
            TextIO.output(outFile, "if-goto "^l1^"\n");
            TextIO.output(outFile, "goto "^l2^"\n");
            TextIO.output(outFile, "label "^l1^"\n");
            List.app (fn s => codegen(s,outFile,bindings,className)) stmt;
            TextIO.output(outFile, "label "^l2^"\n")
          end
        )

    | codegen(ifelse'(e,stmt1,stmt2),outFile,bindings,className) =
        (
          TextIO.output(TextIO.stdOut, "Attempt to compile if-else statement\n");
          let val l1 = nextLabel()
              val l2 = nextLabel()
              val l3 = nextLabel()
          in
            codegen(e,outFile,bindings,className);
            (* TextIO.output(outFile, "not\n"); *)
            TextIO.output(outFile, "if-goto "^l1^"\n");
            TextIO.output(outFile, "goto "^l2^"\n");
            TextIO.output(outFile, "label "^l1^"\n");
            List.app (fn s => codegen(s,outFile,bindings,className)) stmt1;
            TextIO.output(outFile, "goto "^l3^"\n");
            TextIO.output(outFile, "label "^l2^"\n");
            List.app (fn s => codegen(s,outFile,bindings,className)) stmt2;
            TextIO.output(outFile, "label "^l3^"\n")
          end
        )

    | codegen(while'(e,stmt),outFile,bindings,className) =
        (
          TextIO.output(TextIO.stdOut, "Attempt to compile while statement\n");
          let val l1 = nextLabel()
              val l2 = nextLabel()
          in
            TextIO.output(outFile, "label "^l1^"\n");
            codegen(e,outFile,bindings,className);
            TextIO.output(outFile, "not\n");
            TextIO.output(outFile, "if-goto "^l2^"\n");
            List.app (fn s => codegen(s,outFile,bindings,className)) stmt;
            TextIO.output(outFile, "goto "^l1^"\n");
            TextIO.output(outFile, "label "^l2^"\n")
          end
        )
	 
	  | codegen(do'(call),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to call a subroutine with a do statement\n");
        codegen(call,outFile,bindings,className);
        TextIO.output(outFile, "pop temp 0\n")
      )
	 
	  | codegen(subcallq'(id1,id2,exprlist),outFile,bindings,className) =
      (
        let val boo = checkBoundTo(id1,bindings)
        in
          if boo then
          (
            let val (typ,segment,offset) = boundTo(id1,bindings)
            in
              TextIO.output(outFile, "push "^segment^" "^Int.toString(offset)^"\n");
              TextIO.output(TextIO.stdOut, "Attempt to call "^typ^"."^id2^"\n");
              codegenlist(exprlist,outFile,bindings,className);
              TextIO.output(outFile, "call "^typ^"."^id2^" "^(Int.toString((length exprlist)+1))^"\n")
            end
          )
          else
          (
            TextIO.output(TextIO.stdOut, "Attempt to call "^id1^"."^id2^"\n");
            codegenlist(exprlist,outFile,bindings,className);
            TextIO.output(outFile, "call "^id1^"."^id2^" "^(Int.toString(length exprlist))^"\n")
          )
        end
      )

    | codegen(subcall'(id,exprlist),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to call "^id^"\n");
        TextIO.output(outFile, "push pointer 0\n");
        codegenlist(exprlist,outFile,bindings,className);
        TextIO.output(outFile, "call "^className^"."^id^" "^(Int.toString((length exprlist)+1))^"\n")
      )
	 
	  | codegen(returnvoid',outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt returnvoid statement\n");
        TextIO.output(outFile, "push constant 0\nreturn\n")
      )

    | codegen(return'(e),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt return statement\n");
        codegen(e,outFile,bindings,className);
        TextIO.output(outFile, "return\n")
      )

    | codegen(this',outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to compile this\n");
        TextIO.output(outFile, "push pointer 0\n")
      )

    | codegen(id'(id),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to compile identifier\n");
        let val (typ,segment,offset) = boundTo(id,bindings)
        in
          TextIO.output(outFile, "push "^segment^" "^Int.toString(offset)^"\n")
        end
      )

    | codegen(add'(e1,e2),outFile,bindings,className) =
	    (TextIO.output(TextIO.stdOut, "Attempt to compile addition\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "add\n")
      )

    | codegen(sub'(e1,e2),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile subtraction\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "sub\n")
      )

    | codegen(prod'(e1,e2),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile multiplication\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "call Math.multiply 2\n")
      )

    | codegen(div'(e1,e2),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile division\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "call Math.divide 2\n")
      )

    | codegen(and'(e1,e2),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile and\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "and\n")
      )

    | codegen(or'(e1,e2),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile or\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "or\n")
      )

    | codegen(lt'(e1,e2),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile less than\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "lt\n")
      )

    | codegen(gt'(e1,e2),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile greater than\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "gt\n")
      )

    | codegen(negate'(e),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile negate\n");
        codegen(e,outFile,bindings,className);
        TextIO.output(outFile, "neg\n")
      )

    | codegen(not'(e),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile not\n");
        codegen(e,outFile,bindings,className);
        TextIO.output(outFile, "not\n")
      )

    | codegen(true',outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile true\n");
       TextIO.output(outFile, "push constant 0\nnot\n")
      )

    | codegen(false',outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile false\n");
       TextIO.output(outFile, "push constant 0\n")
      )

    | codegen(equal'(e1,e2),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile equal\n");
        codegen(e1,outFile,bindings,className);
        codegen(e2,outFile,bindings,className);
        TextIO.output(outFile, "eq\n")
      )

    | codegen(null',outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to compile null\n");
        TextIO.output(outFile, "push constant 0\n")
      )

    | codegen(integer'(i),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile integer\n");
       TextIO.output(outFile, "push constant "^Int.toString(i)^"\n"))

    | codegen(string'(s),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to compile string\n");
        TextIO.output(outFile, "push constant "^(Int.toString(size s))^"\n");
        TextIO.output(outFile, "call String.new 1\n");
        List.app (fn c => TextIO.output(outFile, "push constant "^(Int.toString(Char.ord c))^"\n" ^
                                "call String.appendChar 2\n")) (String.explode s)
)

    | codegen(_,outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile expression not currently supported!\n");
       raise Unimplemented) 

    and codegenlist([],outFile,bindings,className) = ()
    | codegenlist(h::t,outFile,bindings,className) =
      (codegen(h,outFile,bindings,className);
      codegenlist(t,outFile,bindings,className))

     fun compile filename  = 
         let val (ast, _) = jackparse filename
	     val fileName = hd (String.tokens (fn c => c = #".") filename)
             val outFile = TextIO.openOut(fileName^".vm")
         in
           let val _ = codegen(ast,outFile,[],"")
           in 
             TextIO.closeOut(outFile)
           end
         end 
         handle _ => (TextIO.output(TextIO.stdOut, "An error occurred while compiling!\n\n")); 
             
       
     fun run(a,b::c) = (compile b; OS.Process.success)
       | run(a,b) = (TextIO.print("usage: sml @SMLload=jack\n");
                     OS.Process.success)
end


