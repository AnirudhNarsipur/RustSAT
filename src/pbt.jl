include("./solver.jl")

function is_sound(inst::SATInstance)
    for clause in inst.clauses
        ans = any(map(x -> checkAssignment(inst.varAssignment, x) == Satisfied, clause.literals))
        if !ans
            return false
        end
    end
    true
end
function check_inst(fl::String)
    inst = read_cnf(fl)
    res = _dpll(inst)
    if res isa Bad
        println("Is UNSAT can't check")
    else
    is_sound(inst)
    end
end
function compDict(d1, d2, l)
    k1 = Set(keys(d1))
    k2 = Set(keys(d2))
    @assert k1 == k2
    for key in k1
        if d1[key] == d2[key]
            continue
        else
            error("For ", key, " ", d1[key], " is not ", d2[key], " at level ", l)
        end
    end
end