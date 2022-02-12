include("./dimacparser.jl")
#Checks the watchers of the clause and 
# returns literal if it exists
#guarenteed not to have empty clauses
const ok2 = [Satisfied,Satisfied]
function literalInState(ls,st :: AbstractAssignment)
    any(map(x -> x == st,ls))
end
function allliteralInState(ls,st :: AbstractAssignment)
    all(map(x -> x==st),ls)
end

function checkAssignment(assigments :: Dict,literal :: Number)
   as =  assigments[abs(literal)]
   if (literal < 0 && as == Negative) || (literal > 0 && as == Positive)
    Satisfied
   elseif as == Unset
    Undecided
   else 
    Conflict
   end
end

function checkWatchers(assigs :: Dict{Int,LiteralState} , cls :: Clause)
    if length(cls.watchers) == 0
        cls.literals[1]
    else
        @assert (length(cls.watchers) == 2)
        watcherst = map(x->checkAssignment(assigs,x),cls.watchers)
        if literalInState(watcherst,Satisfied)
            return Satisfied
        elseif literalInState(watcherst,Conflict)
            literalsSt = map(x -> (x,checkAssignment(assigs,cls.literals[x])),1:length(cls.literals))
            #TODO multi filter
            satlit = filter(x -> x[2]==Satisfied,literalsSt)
            undeclit = filter(x->x[2]==Undecided,literalsSt)
            if satlit != []
                for (index,lit) in enumerate(satlit)
                    if index==3
                        break
                    else
                        cls.watchers[index] = lit[1]
                    end
                end
                return Satisfied
            else
                numUndec = length(undeclit)
                if numUndec == 0
                    return Conflict
                elseif numUndec == 1
                    return cls.literals[undeclit[1][1]]
                else
                    @assert numUndec >= 2
                    cls.watchers[1] = undeclit[1][1]
                    cls.watchers[2] = undeclit[2][1]
                    return Satisfied
                end
            end
        end
    end
end
function verify_inst(inst :: SATInstance)
   for i =1:inst.numVars
    @assert inst.varAssignment[i] == Unset
   end
end
#Dumb Just assings everything to Positive
function _dpll(inst :: SATInstance)
    verify_inst(inst)
    function dpll()
        for i=1:inst.numVars
            inst.varAssignment[i] = Positive
        end
    end
    dpll()
    inst
end

function calc_inst(fl :: String)
    inst = read_cnf(fl)
    _dpll(inst)
    giveOutput(fl,1.23,UNSAT)
end
calc_inst(ARGS[1])