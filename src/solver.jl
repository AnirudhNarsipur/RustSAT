module MainModule
include("./dimacparser.jl")
__precompile__()
#Checks the watchers of the clause and 
# returns literal if it exists
#guarenteed not to have empty clauses
const aBad = Bad()
const aNone = None()
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
        aNone
    elseif curr == Conflict
        aBad
    elseif curr == Undecided
        updateStack(inst, literal)
        return aNone
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
                return aNone
            elseif as == Conflict
                return aBad
            elseif as == Undecided
                return Some(cls.literals[1])
            else
                error("not reachable")
            end
        else
            map!(x -> checkAssignment(assigs, cls.literals[x]), watcherst, cls.watchers)
            if literalInState(watcherst, Satisfied)
                return aNone
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
                    return aNone
                else
                    if numUndec == 0
                        return aBad
                    elseif numUndec == 1
                        return Some(cls.literals[undecidedholder[1]])
                    else
                        cls.watchers[1] = undecidedholder[1]
                        cls.watchers[2] = undecidedholder[2]
                        return aNone
                    end
                end
            end
            aNone
        end
        aNone
    end
    return internal
end

function assignLiteral(inst::SATInstance, lit::Number)
    res = setAssignment(inst, lit)
    if res isa Bad
        return aBad
    end
    inst.assigCount = 0
    return aNone
end

function propUnitLiteralsFull(inst::SATInstance, watcherfunc::Function, vr)
    cont = true
    while cont
        cont = false
        for cindex = 1:inst.numClauses
            clause = inst.clauses[cindex]
            res = watcherfunc(clause)
            if res isa None
                continue
            elseif res isa Bad
                return aBad
            elseif res isa Some
                assignLiteral(inst, res.value)
                cont = true
                continue
            else
                error(join("should not be reached res was : ", res))
            end
        end
    end
    return aNone
end
function printClause(inst::SATInstance, c)
    for lit in inst.clauses[c].literals
        print("(", lit, ", ", inst.varAssignment[(abs(lit))], ") ")
    end
    println("")
end

function propUnitLiterals(inst::SATInstance, watcherfunc::Function, vr::T) where {T<:Integer}
    if vr == 0
        return aNone
    end
    res::Option = aBad
    for cindex in getVarClauses(inst, vr)
        res = watcherfunc(inst.clauses[cindex])
        if res isa None
            continue
        elseif res isa Bad
            return aBad
        elseif res isa Some
            assignLiteral(inst, res.value)
            res = propUnitLiterals(inst, watcherfunc, -res.value)
            if res isa Bad
                return res
            end
        else
            error(join("should not be reached res was : ", res))
        end
    end
    return aNone
end
function rand_sign()
    if rand(1:2) == 1
        Positive
    else
        Negative
    end
end
function pickJSW(inst::SATInstance,jswraw :: Vector{Pair{Vector{T},Vector{Float16}}}) where T <: Integer
    foreach(x -> jswraw[x][2][1] = 0.0,1:inst.numVars)
    clause_len = 0
    all_sat = true
    for clause in inst.clauses
        clause_sat = false
        for literal in clause.literals
            if checkAssignment(inst.varAssignment, literal) == Satisfied
                clause_sat = true
                break
            end
        end
        if !clause_sat
            all_sat = false
            clause_len = length(clause.literals)
            for literal in clause.literals
                jswraw[abs(literal)][2][1] += (2.0)^(-clause_len)
            end
        end
    end
    if all_sat
        return aNone
    else
        sort!(jswraw, by = x -> x[2][1], rev = true, alg = QuickSort)
        function internal()
            for (lit, val) in jswraw
                if inst.varAssignment[lit[1]] == Unset
                    return Some((lit[1], rand_sign()))
                else
                    continue
                end
            end
            return aBad
        end
        Some(internal)
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
            return aBad
        end
    end
    return aNone
end
function isSatisified(inst::SATInstance)
    for clause in inst.clauses
        for lit in clause.literals
            if checkAssignment(inst.varAssignment, lit) == Satisfied
                continue
            end
            return false
        end
    end
    return true
end
function to_sign(l::LiteralState)
    if l == Positive
        return 1
    elseif l == Negative
        return -1
    else
        error("bad")
    end
end
function _dpll(inst::SATInstance)
    # verify_inst(inst)
    jswraw = Vector{Pair{Vector{inst.signedtp},Vector{Float16}}}(undef, inst.numVars)
    foreach(x -> jswraw[x] = Pair([x],[0.0]),1:inst.numVars)
    watcherfunc = checkWatchers(inst)
    pickVar = pickJSW(inst,jswraw)
    if pickVar isa None
        return aNone
    else
        pickVar = pickVar.value
    end
    pureLitfunc = pureLiteralElimination(inst)
    propUnitLiteralsFull(inst, watcherfunc, 0)
    pureLitfunc()
    proptime = 0
    function dpll(vr::T) where {T<:Integer}
        #BCP
        
        if inst.assigCount > 2
            res = pickJSW(inst,jswraw)
            if res isa None
                return aNone
            else
                pickVar = res.value
                inst.assigCount = 0
            end
        end
        inst.assigCount += 1
        newStackCall(inst)
        start = Base.Libc.time()
        res = propUnitLiterals(inst, watcherfunc, -vr)
        fin = Base.Libc.time()
        proptime += (fin - start)
        if res isa Bad
            unwindStack(inst)
            return res
        else
            VTB = pickVar()
            if VTB isa Bad
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
    println("proptime is ", proptime)
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
# calc_inst("small_inst/toy_solveable.cnf")