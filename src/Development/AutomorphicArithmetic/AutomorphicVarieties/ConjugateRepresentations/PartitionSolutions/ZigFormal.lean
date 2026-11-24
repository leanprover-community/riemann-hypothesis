module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.zigFormal :
    ZigFormal := by
  intro Γ V S I _ _ _ _ d G
  refine ⟨fun q k u u' c h hz => ?_, fun ι hι q => ?_⟩
  · cases q with
    | zero => exact fun x hx => (h x hx).symm.trans (hz x hx)
    | succ q =>
      obtain ⟨b, hb, hdb, hz⟩ := hz
      exact ⟨b, hb, fun x hx => (hdb x hx).trans (h x hx), hz⟩
  · induction q with
    | zero => exact fun k u c hz x hx => hz (x.map ι) (by rw [List.length_map, hx])
    | succ q ih =>
      rintro k u c ⟨b, hb, hdb, hz⟩
      refine ⟨fun x => b (x.map ι), fun γ x hx => ?_, fun x hx => hdb (x.map ι) (by rw [List.length_map, hx]), ?_⟩
      · have h := hb γ (x.map ι) (by rw [List.length_map, hx])
        refine Eq.trans ?_ h
        simp only [List.map_map]
        congr 2
        funext δ
        exact hι γ δ
      · have h := ih (k + 1) _ c hz
        have e : (fun x : List Γ => UpperTheory.V.Lit.Geo.hd b (x.map ι)) = UpperTheory.V.Lit.Geo.hd (fun x : List Γ => b (x.map ι)) :=
          funext fun x => (hdFacts.2.2.1 I Γ _ ι b x).symm
        rw [e] at h
        exact h
