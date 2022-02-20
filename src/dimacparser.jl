include("datastructs.jl")
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
            satinstance = initializeInstance(numVars, numClauses)
           
            literals = Vector{satinstance.signedtp}(undef,numVars)
            for (index, rawclause) in enumerate(itr)
                if rawclause == ""
                    continue
                end
                tmp = split(rawclause)
                map!(x -> parse(satinstance.signedtp, x),literals, tmp)
                clause = getClause(literals[1:length(tmp)-1] , satinstance.signedtp)
                if clause==nothing
                    giveOutput(fl,0,UNSAT)
                end
                satinstance.clauses[index] = clause
                updateVarClause(satinstance)
            end
            return satinstance
        end
    catch
        error("Could not read CNF file")
    end
end
function assigStrRep(assig :: Dict)
    strres = Vector{String}(undef,length(assig))
    for v in assig
        if v[2] == Positive
            strres[v[1]] = join([string(v[1])," true "])
        elseif v[2] == Negative
            strres[v[1]] = join([string(v[1])," false "])
        elseif v[2] == Unset
            println("v is ",v[1]," ",v[2])
            strres[v[1]] = join([string(v[1])," true "])
        else
            error("cant even")
        end
    end
    return strres
end

function giveOutput(fl :: String,time ,result :: Satisfiability)
   kv_json = (k,v) -> join(['"',k,"""": """,'"',v,'"'])
   time = round(time,digits=2)
   if result isa UNSAT
    out = join([
        "{",
        kv_json("Instance",fl),",",
        kv_json("Time",time),",",
        kv_json("Result","UNSAT") ,
        "}"
    ])
   println(out)
   return nothing
   else
    strrep = strip(join(assigStrRep(result.assignment)))
    out = join([
        "{",
        kv_json("Instance",fl),",",
        kv_json("Time",time),",",
        kv_json("Result","SAT"),"," ,
        kv_json("Solution",strrep),
        "}"
    ],"")
    println(out)
    return nothing
   end
end


    






