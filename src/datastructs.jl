# Marks whether a literal is satisified , in conflict or undecided

@enum AbstractAssignment::Int8 Satisfied Conflict Undecided
@enum LiteralState::Int8 Positive Negative Unset
abstract type Option end
struct Some{T} <: Option
    value::T
end
struct None <: Option end
struct Bad <: Option end
struct Skip <: Option end
abstract type Satisfiability end
struct SAT{T} <: Satisfiability
    assignment::Dict{T,LiteralState}
end
struct UNSAT <: Satisfiability end
mutable struct DynamicVec{T}
    top::UInt64
    vec::Vector{T}
end
# Holds a the literals of a clause and it's watchers (2 watchers)
#watchers holds indices not literals

struct Clause{T}
    literals::Vector{T}
    watchers::Vector{T}
end
Base.:(==)(x::Clause, y::Clause) = x.literals == y.literals && x.watchers == y.watchers
mutable struct SATInstance{T,K}
    usignedtp::Type
    signedtp::Type
    numVars::T
    numClauses::T
    varAssignment::Dict{T,LiteralState}
    clauses::Vector{Clause{K}}
    decisionStack::DynamicVec{DynamicVec{T}}
    varClause :: Vector{Pair{DynamicVec{T},DynamicVec{T}}}
    assigCount :: Int16
end
function initializeDynamicVec(tp::Type)
    DynamicVec{tp}(0, Vector{tp}(undef, 1))

end
function pushElem(dvec::DynamicVec{T}, elem::T) where {T}
    ln = length(dvec.vec)
    if dvec.top == ln
        resize!(dvec.vec, ln * 2)
    end 
    dvec.vec[dvec.top+1] = elem
    dvec.top += 1
end
function popElem(dvec::DynamicVec{T}) where {T}
    if dvec.top == 0
        Bad()
    else
        tmp = dvec.vec[dvec.top]
        dvec.top -= 1
        return Some(tmp)
    end
end
function viewDvec(dvec :: DynamicVec{T}) where {T}
        return view(dvec.vec,1:dvec.top)
end
function pop2DElem(dvec :: DynamicVec{DynamicVec{T}}) where {T}
    if dvec.top == 0
        return Bad()
    else
        tmp = dvec.vec[dvec.top]
        dvec.top -= 1
        if tmp.top == 0
           return Bad()
        else
            return Some(view(tmp.vec,1:tmp.top))
        end         
    end 
end
function push2DElem(dvec :: DynamicVec{DynamicVec{T}},elem :: T) where {T}
    if dvec.top == 0
        pushElem(dvec,initializeDynamicVec(T))
    end
    pushElem(dvec.vec[dvec.top],elem)
    return nothing
end
function initializeVarClause(numVars :: Number,tp::Type)
    varClause = Vector{Pair{DynamicVec{tp},DynamicVec{tp}}}()
    resize!(varClause,numVars)
    for index=1:numVars
        varClause[index] = Pair(initializeDynamicVec(tp),initializeDynamicVec(tp))
    end
    varClause
end
function initializeInstance(vars::Number, clauses::Number)
    sattp = getnumtype(clauses, vars)
    clausevec = Vector{Clause{sattp.second}}(undef, clauses)
    resize!(clausevec,clauses)
    SATType = SATInstance{sattp...}
    assigs = map(x -> (abs(x), Unset), 1:vars)
    varClause = initializeVarClause(vars,sattp.first)
    SATType(sattp.first, sattp.second, vars, clauses, Dict(assigs), clausevec,initializeDynamicVec(DynamicVec{sattp.first}),varClause,0)
end
function getClause(literals, tp::Type)
    @assert !(0 in literals)
    ltrslen = length(literals)
    if ltrslen == 0
        return nothing
    elseif ltrslen == 1
        Clause{tp}(literals, [])
    else
        Clause{tp}(literals, [1, 2])
    end
end
# Given num of clauses and vars calculates approp num type
function getnumtype(clauses::Number, vars::Number)
    choose = clauses > vars ? clauses : vars
    tps = [Int8, Int16, Int32, Int64, Int128]
    mapping = Dict(
        Int8 => UInt8,
        Int16 => UInt16,
        Int32 => UInt32,
        Int64 => UInt64,
        Int128 => UInt128,
    )
    for tp in tps
        if choose < typemax(tp)
            return Pair(mapping[tp], tp)
        end
    end
    error("Clause set is too large Overflow")
end
# Update varClause index with results from clause at index
function updateVarClause(inst :: SATInstance,index :: Number)
    ablit = 0
    for lit in inst.clauses[index].literals 
        ablit = abs(lit)
        if ablit == lit 
            pushElem(inst.varClause[ablit].first,convert(inst.usignedtp, index))
        else
            pushElem(inst.varClause[ablit].second,convert(inst.usignedtp, index))
        end
    end
end
function getVarClauses(inst :: SATInstance,lit :: T) where T <: Integer
    if sign(lit) == 1
        return viewDvec(inst.varClause[lit].first)
    else
        return viewDvec(inst.varClause[abs(lit)].second)
    end
end