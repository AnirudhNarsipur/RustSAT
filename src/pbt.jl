include("./solver.jl")

function is_sound(inst :: SATInstance)
    for clause in inst.clauses
        ans = any(map(x ->checkAssignment(inst.varAssignment,x)==Satisfied,clause.literals))
        if !ans
            return false
        end
    end
    true
end
function check_inst(fl :: String)
    inst = read_cnf(fl)
    p_dpll(inst)
    println("inst is sound? ",is_sound(inst))
    return nothing
end
check_inst("input/C168_128.cnf")