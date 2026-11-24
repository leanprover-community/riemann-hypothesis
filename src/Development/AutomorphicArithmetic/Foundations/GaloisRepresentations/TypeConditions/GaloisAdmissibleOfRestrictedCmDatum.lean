module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.GalC.Tr

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem galois_admissible_of_restricted_cmDatum {D : D7} {c : CutD D} (h : UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut) :
    UpperTheory.GalS.AutomorphicGaloisAdmissible (cut D c).nd (cut D c).naut := fun i =>
  ⟨fun a ha π hc hr => by
    obtain ⟨ρ, c1, s, o, u, e⟩ := (h i.1).1 a ha π hc hr
    exact ⟨ρ, c1, s, fun w hw => ⟨(o w hw).dim, (o w hw).eq_of_unr, (o w hw).ine, (o w hw).mono⟩,
      fun w hw g => ⟨(u w hw g).1, (u w hw g).2.1, ⟨(u w hw g).2.2.rel.dim, (u w hw g).2.2.rel.mono, (u w hw g).2.2.rel.ine⟩,
        (u w hw g).2.2.one⟩, e⟩, (h i.1).2⟩

end UpperTheory.GalC.Tr
