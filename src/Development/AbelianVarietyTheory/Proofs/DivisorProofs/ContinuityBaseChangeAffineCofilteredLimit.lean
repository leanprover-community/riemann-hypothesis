module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSchBc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

private theorem eqv_of_isIso' (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := by
  intro n
  refine ⟨fun x y hxy => ?_, fun x => ⟨pull R (inv f) F n x, ?_⟩⟩
  · have hx := pull_comp R (inv f) f F n x
    have hy := pull_comp R (inv f) f F n y
    rw [IsIso.inv_hom_id, pull_id] at hx hy
    rw [hx, hy, hxy]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem contCone_bc_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S), IsAffine W → ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F hF S I _ _ G c hc hG W r hW
  haveI : IsConnected I := IsCofiltered.isConnected I
  obtain ⟨e, -⟩ := bc_sch_iso S W r
  let P : Over S ⥤ Scheme.{0} := Over.pullback r ⋙ Over.forget W
  have hlim : IsLimit (P.mapCone c) := isLimitOfPreserves P hc
  have haff : ∀ i, IsAffine ((G ⋙ P).obj i) := by
    intro i
    change IsAffine (pullback (G.obj i).hom r)
    haveI := hG i
    exact isAffine_of_isAffineHom (pullback.snd (G.obj i).hom r)
  have h1 : ContCone R F (sch.mapCone (P.mapCone c)) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I (G ⋙ P) (P.mapCone c) hlim haff
  let α : (G ⋙ P) ⋙ sch ⟶ G ⋙ bc (sch.map r) :=
    { app := fun i => e.hom.app (G.obj i)
      naturality := fun i j f => e.hom.naturality (G.map f) }
  refine (ContCone.iff_of_eqv R F I _ _ (sch.mapCone (P.mapCone c)) ((bc (sch.map r)).mapCone c) α (e.hom.app c.pt)
    (fun i => e.hom.naturality (c.π.app i)) (fun i => eqv_of_isIso' R F _) (eqv_of_isIso' R F _)).1 h1

end GlobalTheory.EtC
