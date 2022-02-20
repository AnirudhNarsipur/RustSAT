include("./solver.jl")
function propUnitpureLit(inst::SATInstance, watcherfunc::Function)
    purelit = Vector{Int8}(undef, inst.numVars)
    fill!(purelit, 0)
    signlit::Int8 = 0
    absLit::inst.usignedtp = 0
    function calcPureLit(clause::Clause)
        for literal in clause.literals
            abslit = abs(literal)
            signlit = sign(literal)
            if inst.varAssignment[abslit] != Unset
                continue
            elseif purelit[abslit] == 0
                purelit[abslit] = signlit
            elseif purelit[abslit] == 1 && signlit == -1
                purelit[abslit] = 2
            elseif purelit[abslit] == -1 && signlit == 1
                purelit[abslit] = 2
            else
                continue
            end
        end
    end

    function assignPureLits()
        for (lit, value) in enumerate(purelit)
            if value == 1 || value == -1
                assignLiteral(inst, value * lit)
            else
                continue
            end
        end
    end
    cont = true
    while cont
        cont = false
        for clause in inst.clauses
            res = watcherfunc(clause)
            if res isa Skip
                continue
            elseif res isa None
                calcPureLit(clause)
                continue
            elseif res isa Bad
                return Bad()
            elseif res isa Some || res isa Skip
                calcPureLit(clause)
                assignLiteral(inst, res.value)
                cont = true
                continue
            else
                error(join("should not be reached res was : ", res))
            end
        end
    end
    assignPureLits()
    return None()
end
function verify_inst(inst::SATInstance)
    @assert length(keys(inst.varAssignment)) == inst.numVars
    for i = 1:inst.numVars
        @assert inst.varAssignment[i] == Unset
    end
    for key in keys(inst.varAssignment)
        @assert 1 <= key <= inst.numVars
    end
end
# 1 - Positive -1 : Negative 0 : Undefined 2 : Mixed
function pureLiteralElimination(inst::SATInstance)
    purelit = Vector{Int8}(undef, inst.numVars)
    fill!(purelit, 0)
    signlit::Int8 = 0
    absLit::inst.usignedtp = 0
    function internal()
        fill!(purelit, 0)
        for clause in inst.clauses
            for literal in clause.literals
                abslit = abs(literal)
                signlit = sign(literal)
                if inst.varAssignment[abslit] != Unset
                    continue
                elseif purelit[abslit] == 0
                    purelit[abslit] = signlit
                elseif purelit[abslit] == 1 && signlit == -1
                    purelit[abslit] = 2
                elseif purelit[abslit] == -1 && signlit == 1
                    purelit[abslit] = 2
                else
                    continue
                end
            end
        end
        for (lit, value) in enumerate(purelit)
            if value == 1
                inst.varAssignment[lit] = Positive
            elseif value == -1
                inst.varAssignment[lit] = Negative
            else
                continue
            end
        end
    end
    return internal
end