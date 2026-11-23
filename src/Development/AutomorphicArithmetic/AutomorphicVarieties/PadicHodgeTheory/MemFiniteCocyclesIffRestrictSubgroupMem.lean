module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem :
    ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ β ∈ Z1 T.M1, (β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1 ↔ (fun g : H => (β g).1) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1)) ∧ (fun g : H => (β g).2) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2))) := by
  intro l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT β hβ
  haveI := hD.normal
  haveI := hD.fin
  have hM : ∀ (g : H) (v : B × B), (T.M1.comp H.subtype : Representation B H (B × B)) g v =
      (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1) g v.1, chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2) g v.2) := by
    intro g v
    change T.M1 g v = _
    rw [Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    rfl
  rw [z1fDesc (MonoidHom.id (GQ l)) T.M1 H β hβ, MonoidHom.id_comp]
  constructor
  · intro h
    exact ⟨(z1fMap H.subtype _ _).2 (LinearMap.fst ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h,
      (z1fMap H.subtype _ _).2 (LinearMap.snd ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h⟩
  · rintro ⟨h1, h2⟩
    have k1 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inl ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h1
    have k2 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inr ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h2
    have k := add_mem k1 k2
    convert k using 1
    ext g <;> simp
