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
          codegenlist(subroutines,outFile,bindingsNew@bindings,id)
        end
      )

    | codegen(constructor'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
	      TextIO.output(TextIO.stdOut, "Attempt to compile constructor named "^id^"\n")

    | codegen(function'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
	    (
        TextIO.output(TextIO.stdOut, "Attempt to compile function named "^id^"\n");
        TextIO.output(outFile,"function "^className^"."^id^" "^Int.toString(length vardecs)^"\n");
        codegenlist(statements,outFile,bindings,className)
      )

    | codegen(method'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
	      TextIO.output(TextIO.stdOut, "Attempt to compile method named "^id^"\n")
	 
	  | codegen(do'(call),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to call a subroutine with a do statement\n");
        codegen(call,outFile,bindings,className);
        TextIO.output(outFile, "pop temp 0\n")
      )
	 
	  | codegen(subcallq'(id1,id2,exprlist),outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt to call "^id1^"."^id2^"\n");
        codegenlist(exprlist,outFile,bindings,className);
        TextIO.output(outFile, "call "^id1^"."^id2^" "^(Int.toString(length exprlist))^"\n")
      )
	 
	  | codegen(returnvoid',outFile,bindings,className) =
      (
        TextIO.output(TextIO.stdOut, "Attempt returnvoid statement\n");
        TextIO.output(outFile, "push constant 0\nreturn\n")
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

    | codegen(integer'(i),outFile,bindings,className) =
      (TextIO.output(TextIO.stdOut, "Attempt to compile integer\n");
       TextIO.output(outFile, "push constant "^Int.toString(i)^"\n"))

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


