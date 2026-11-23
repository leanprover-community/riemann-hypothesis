module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.LiftEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.FSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepGens
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem lift_eq' {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) C) (z : MonoidAlgebra B G) :
    MonoidAlgebra.lift B _ G ρ z = GDet.repAlg ρ C (MonoidAlgebra.mapRingHom G (algebraMap B C) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add (f := _), hf, hg, map_add (f := _), map_add (f := _)]
  | single g b =>
    simp [GDet.repAlg, MonoidAlgebra.lift_single, algebraMap_smul]

theorem UpperTheory.V.Pa.rep_quot :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∃ ρ : u.D.CHQuot P.gens →+* Matrix (Fin n) (Fin n) x.A, ∀ y, ρ (u.D.toQuot P.gens y) = P.rep y := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P
  letI : Algebra B x.A := P.f.toRingHom.toAlgebra
  haveI : CompactSpace G.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.η_open).isCompact
  have hp : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _
  have h1 : maximalIdeal B ≤ Ideal.comap (algebraMap B x.A) (maximalIdeal x.A) := by
    intro b hb
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    haveI := (f_surj P).2
    exact (mem_maximalIdeal _).mp hb (isUnit_of_map_unit P.f.toRingHom b hu)
  have h2 : ∀ a b : Fin n, AdicCont (maximalIdeal x.A) fun g ↦ (mat (x.ρ.comp h.p₀)) g a b := by
    intro a b N
    exact (x.cont a b N).comp_continuous hp
  have h3 : u.D.map (algebraMap B x.A) = GDet.ofRep (mat (x.ρ.comp h.p₀)) := P.maps.1
  have h4 : ∀ z ∈ P.gens,
      MonoidAlgebra.lift B (Matrix (Fin n) (Fin n) x.A) G.G₀ (mat (x.ρ.comp h.p₀)) z = 0 := by
    intro z hz
    rw [lift_eq']
    exact rep_gens P z hz
  obtain ⟨ρ, hρ⟩ := f_rep (maximalIdeal x.A) u.D (mat (x.ρ.comp h.p₀)) P.gens h1 h2 h3 h4
  refine ⟨ρ.toRingHom, fun y => ?_⟩
  have hext : ρ.comp (u.D.toQuot P.gens) = MonoidAlgebra.lift B _ G.G₀ (mat (x.ρ.comp h.p₀)) :=
    MonoidAlgebra.algHom_ext (fun g => by simp [hρ]) (Subsingleton.elim _ _)
  have hy := congrArg (fun φ => φ y) hext
  simp only [AlgHom.comp_apply] at hy
  change ρ (u.D.toQuot P.gens y) = _
  rw [hy, lift_eq']
  rfl
