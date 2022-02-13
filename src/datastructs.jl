# Marks whether a literal is satisified , in conflict or undecided

@enum AbstractAssignment::Int8 Satisfied Conflict Undecided
@enum LiteralState::Int8 Positive Negative Unset
abstract type Option end
struct Some{T} <: Option
    value :: T
end
struct None <: Option end
struct Bad <: Option end
abstract type Satisfiability end
struct SAT{T} <: Satisfiability
    assignment :: Dict{T,LiteralState}
end
struct UNSAT <: Satisfiability end
# Constant for debugging
# Holds a the literals of a clause and it's watchers (2 watchers)
#watchers holds indices not literals
mutable struct Clause{T}
    literals::Vector{T}
    watchers::Vector{T}
end
Base.:(==)(x::Clause, y::Clause) = x.literals == y.literals && x.watchers == y.watchers
mutable struct VarClause{T}
    posLiteral::Vector{T}
    negLiteral::Vector{T}
end
mutable struct SATInstance{T,K}
    usignedtp :: Type
    signedtp :: Type
    numVars::T
    numClauses::T
    varAssignment::Dict{T,LiteralState}
    clauses::Vector{Clause{K}}
    decisionStack :: Vector{Vector{T}}
end


function initializeInstance(vars :: Number, clauses :: Number)
    sattp = getnumtype(clauses,vars)
    clausevec = Vector{Clause{sattp.second}}(undef, clauses)
    SATType = SATInstance{sattp...}
    assigs = map(x -> (abs(x),Unset),1:vars)
    SATType(sattp.first,sattp.second,vars, clauses, Dict(assigs), clausevec,[])
end
function getClause(literals , tp :: Type)
    @assert !(0 in literals)
    ltrslen = length(literals)
    if ltrslen == 0
        return nothing
    elseif ltrslen == 1
        Clause{tp}(literals, [])
    else
         Clause{tp}(literals, [1,2])
    end
end
# Given num of clauses and vars calculates approp num type
function getnumtype(clauses :: Number,vars :: Number)
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
function addToVarClause(instance::SATInstance, watchers, index)
    for watcher in watchers
        abwatch = abs(watcher)
        if haskey(instance.varToClause, abwatch)
            (abwatch == watcher) ? push!(instance.varToClause[abwatch].posLiteral, index) :
            push!(instance.varToClause[abwatch].negLiteral, index)
        else
            (abwatch == watcher) ? instance.varToClause[abwatch] = VarClause([convert(instance.usignedtp,index)],Vector{instance.usignedtp}()) :
            instance.varToClause[abwatch] = VarClause(Vector{instance.usignedtp}(),[convert(instance.usignedtp,index)])
        end
    end
end