include("datastructs.jl")
# showstruct(inst :: SATInstance) = println( "
#  numVars: $(inst.numVars), 
#  numClauses :  $(inst.numVars) \n
#  varAssignment: $(inst.varAssignment) \n
#  clauses: $(inst.clauses) \n 
#  varToClause:  $(inst.varToClause) \n")


function read_cnf(fl::String)
    try
        open(fl, "r") do io
            itr = eachline(io)
            numVars = 0
            numClauses = 0
            SATType = SATInstance{UInt64,Int64}
            for line in itr
                if line[1] == 'c'
                    continue
                end
                if line[1] == 'p'
                    pln = split(line)
                    numVars = parse(UInt128, pln[3])
                    numClauses = parse(UInt128, pln[4])
                    break
                end
            end
            #Remove redundancy here
            sattp = getnumtype(numClauses,numVars)
            satinstance = initializeInstance(numVars, numClauses)
            # if debug
            #     println("SAT Instance is ", satinstance)

            #     println("sattp is ", sattp)
            # end
            resize!(satinstance.clauses,numClauses)
            for (index, rawclause) in enumerate(itr)
                if rawclause == ""
                    continue
                end
                # println("split :", split(clause))
                literals = map(x -> parse(sattp.second, x), split(rawclause))
                # println(nums)
                # @assert last(literals) == 0
                clause = getClause(literals, sattp.second)
                if clause==nothing
                    giveOutput(UNSAT)
                end
                addToVarClause(satinstance, clause.watchers,index)
                satinstance.clauses[index] = clause
            end
            # showstruct(satinstance)
            # println("Size of instance ",sizeof(satinstance)) 
            return satinstance
        end
    catch
        error("Could not read CNF file")
    end
end

function giveOutput(fl :: String,time ,result)
   kv_json = (k,v) -> join(['"',k,""" ": """,'"',v,'"'])
   out = join([
       "{",
       kv_json("Instance",fl),",",
       kv_json("Time",time),",",
       kv_json("Result","UNSAT") ,
       "}"
   ])
   print(out)
end

    






