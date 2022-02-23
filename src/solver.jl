module MainModule
include("./dimacparser.jl")
__precompile__()
#Checks the watchers of the clause and 
# returns literal if it exists
#guarenteed not to have empty clauses
const aBad = Bad()
function literalInState(ls::Vector{AbstractAssignment}, st::AbstractAssignment)
    for elem in ls
        if elem == st
            return true

        end
    end
    return false
end

function checkAssignment(assigments::Dict{T,LiteralState}, literal::Number) where {T<:Number}
    as = assigments[abs(literal)]
    if (literal < 0 && as == Negative) || (literal > 0 && as == Positive)
        return Satisfied
    elseif as == Unset
        return Undecided
    else
        return Conflict
    end
end
function updateStack(inst::SATInstance, literal::Number)
    # println("pushing ",literal," at level ",length(inst.decisionStack))
    # @assert 1 <= convert(inst.usignedtp, abs(literal)) <= inst.numVars
    inst.varAssignment[abs(literal)] = (literal > 0) ? Positive : Negative
    push2DElem(inst.decisionStack, convert(inst.usignedtp, abs(literal)))
    return nothing
end
function newStackCall(inst::SATInstance)
    pushElem(inst.decisionStack, initializeDynamicVec(inst.usignedtp))
end
function unwindStack(inst::SATInstance)
    last = pop2DElem(inst.decisionStack)
    if last isa Bad
        return nothing
    elseif last isa Some
        # println("last is  ",last.value.vec)
        for i in last.value
            # println("i is ",i)
            # @assert 1 <= i <= inst.numVars
            inst.varAssignment[i] = Unset
        end
        return nothing
    else
        error("unreachable!")
    end
end

function setAssignment(inst::SATInstance, literal::Number)
    curr = checkAssignment(inst.varAssignment, literal)
    if curr == Satisfied
        None()
    elseif curr == Conflict
        Bad()
    elseif curr == Undecided
        updateStack(inst, literal)
        return None()
    else
        error("should not be reached")
    end
end
# Returns Option
function checkWatchers(inst::SATInstance) where {T}
    assigs = inst.varAssignment
    watcherst = Vector{AbstractAssignment}(undef, 2)
    literalsholder = Vector{Tuple{inst.signedtp,AbstractAssignment}}(undef, inst.numVars)
    undecidedholder = [1, 2]
    watcherstloop::AbstractAssignment = Undecided
    cflc::Bool = true
    function internal(cls::Clause{K}) where {K}
        if length(cls.watchers) == 0
            as = checkAssignment(assigs, cls.literals[1])
            if as == Satisfied
                return Skip()
            elseif as == Conflict
                return Bad()
            elseif as == Undecided
                return Some(cls.literals[1])
            else
                error("not reachable")
            end
        else
            map!(x -> checkAssignment(assigs, cls.literals[x]), watcherst, cls.watchers)
            if literalInState(watcherst, Satisfied)
                return Skip()
            elseif literalInState(watcherst, Conflict)
                lnlit = length(cls.literals)
                map!(x -> (x, checkAssignment(assigs, cls.literals[x])), literalsholder, 1:lnlit)
                # literalsSt = map(x -> (x, checkAssignment(assigs, cls.literals[x])), 1:length(cls.literals))
                #TODO multi filter
                literalsSt = view(literalsholder, 1:lnlit)
                setsat = 1
                numUndec = 0
                for i = 1:lnlit
                    lit = literalsSt[i]
                    if setsat == 3 || numUndec == 2
                        break
                    elseif lit[2] == Satisfied
                        cls.watchers[setsat] = lit[1]
                        setsat += 1
                    elseif lit[2] == Undecided
                        numUndec += 1
                        undecidedholder[numUndec] = i

                    end
                end
                if setsat != 1
                    return Skip()
                else
                    if numUndec == 0
                        return aBad
                    elseif numUndec == 1
                        return Some(cls.literals[undecidedholder[1]])
                    else
                        cls.watchers[1] = undecidedholder[1]
                        cls.watchers[2] = undecidedholder[2]
                        return None()
                    end
                end
            end
            None()
        end
        None()
    end
    return internal
end

function assignLiteral(inst::SATInstance, lit::Number)
    inst.assigCount = 0
    res = setAssignment(inst, lit)
    if res isa Bad
        return Bad
    end
    return None
end

function propUnitLiteralsFull(inst::SATInstance, watcherfunc::Function,vr :: T) where T <: Integer
    cont = true
    while cont
        cont = false
        for cindex =1:inst.numClauses
            clause = inst.clauses[cindex]
            res = watcherfunc(clause)
            if res isa None || res isa Skip
                continue
            elseif res isa Bad
                # print("Returning bad at cindex ",cindex," vr : ",vr, " clause : ")
                # printClause(inst,cindex)
                return Bad()
            elseif res isa Some
                # if dp == 2
                #     println("assigning ",res.value," from index ",cindex)
                # end
                assignLiteral(inst, res.value)
                cont = true
                continue
            else
                error(join("should not be reached res was : ", res))
            end
        end
    end
    return None()
end
function printClause(inst :: SATInstance,c )
    for lit in inst.clauses[c].literals
        print("(",lit,", ",inst.varAssignment[(abs(lit))],") ")
    end
    println("")   
end

function propUnitLiterals(inst::SATInstance, watcherfunc::Function, vr::T) where {T<:Integer}
    if vr == 0
        return None()
    end
    res::Option = aBad
    for cindex in getVarClauses(inst,vr)
        res = watcherfunc(inst.clauses[cindex])
        if res isa None || res isa Skip
            continue
        elseif res isa Bad
            return Bad()
        elseif res isa Some
            assignLiteral(inst, res.value)
            res = propUnitLiterals(inst,watcherfunc,-res.value)
            if res isa Bad
                return Bad()
            end
        else
            error(join("should not be reached res was : ", res))
        end
    end
    return None()
end

function pickJSW(inst::SATInstance)
    jswraw = Vector{Float16}(undef, inst.numVars)
    fill!(jswraw, 0.0)
    clause_len = 0
    t = 0
    for clause in inst.clauses
        clause_len = length(clause.literals)
        is_sat = false
        for literal in clause.literals
            if checkAssignment(inst.varAssignment, literal) == Satisfied
                is_sat = true
                break
            end
        end
        if !is_sat
            for literal in clause.literals
                jswraw[abs(literal)] += (2.0)^(-clause_len)
            end
        end
    end
    jswpair = [(index, val) for (index, val) in enumerate(jswraw)]
    sort!(jswpair, by = x -> x[2], rev = true)
    function internal()
        for (lit, val) in jswpair
            if inst.varAssignment[lit] == Unset
                return Some((lit, Positive))
            else
                continue
            end
        end
        return None()
    end
end

function opposite(x::LiteralState)
    if x == Positive
        Negative
    elseif x == Negative
        Positive
    else
        error("bad")
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
function checkConflict(inst::SATInstance, watcherfunc::Function)
    res::Option = None()
    for clause in inst.clauses
        res = watcherfunc(clause)
        if res isa Bad
            return Bad()
        end
    end
    return None()
end
function isSatisfied(inst :: SATInstance,watcherfunc :: Function)
    for clause in inst.clauses
        res = watcherfunc(clause)
        if !(res isa Skip)
            return false
        end
    end
    return true
end
function _dpll(inst::SATInstance)
    # verify_inst(inst)
    watcherfunc = checkWatchers(inst)
    pickVar = pickJSW(inst)
    pureLitfunc = pureLiteralElimination(inst)
    propUnitLiteralsFull(inst, watcherfunc,0)
    # pureLitfunc()
    proptime = 0
    # dpp = 0
    function dpll(vr::T) where {T<:Integer}
        #BCP
        # dpp+=1
        # println("at ",dpp," vr is ",vr)
        inst.assigCount+=1
        newStackCall(inst)
        start = Base.Libc.time()
        res = propUnitLiterals(inst, watcherfunc,-vr)
        fin = Base.Libc.time()
        proptime += (fin - start)
        if inst.assigCount > 3 && isSatisfied(inst,watcherfunc)
            return None()
        end
        if res isa Bad
            unwindStack(inst)
            return res
        else
            VTB = pickVar()
            if VTB isa None
                return checkConflict(inst, watcherfunc)
            else
                VTB = VTB.value
                inst.varAssignment[VTB[1]] = Positive
                res = dpll(VTB[1])
                if res isa None
                    return res
                else
                    inst.varAssignment[VTB[1]] = Negative
                    res = dpll(-VTB[1])
                    if res isa Bad
                        inst.varAssignment[VTB[1]] = Unset
                        unwindStack(inst)
                    end
                    return res
                end
            end
        end
    end
    rs = dpll(0)
    # println("proptime is ", proptime," dpp is ",dpp)
    return rs
end

function calc_inst(fl::String)
    start_time = Base.Libc.time()
    inst = read_cnf(fl)
    res = _dpll(inst)
    end_time = Base.Libc.time()
    total_time = end_time - start_time
    if res isa None
        giveOutput(fl, total_time, SAT(inst.varAssignment))
    elseif res isa Bad
        giveOutput(fl, total_time, UNSAT())
    else
        error("why oh why", res)
    end
end
function __init__()
    calc_inst(ARGS[1])
end
end
# calc_inst("small_inst/toy_solveable.cnf")
# calc_inst("test_inst/test4.cnf")
# @time calc_inst("input/C208_120.cnf")