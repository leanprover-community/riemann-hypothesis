module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusQuotientNoCocharacter
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusHomEqOneOfNoCocharacterStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem nonempty_torusExtension_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G₁ : Over (Sp k)) [GrpObj G] [GrpObj G₁], SmConn G₁ → Nonempty (TorusExtension G) → ∀ r : G ⟶ G₁, IsMonHom r → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G₁), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ r = y) → Nonempty (TorusExtension G₁) := by
  intro k _ _ G G₁ _ _ hG₁ ⟨E⟩ r hr hsurj
  obtain ⟨X, _, _, _, B₁, _, i₁, q₁, ⟨hi, hq, hfl, hsu, haf, hker, hc, hsm, hsep, hqc, hgc⟩, hno⟩ :=
    MaxTorus.exists_quot_no_cocharacter k G₁ hG₁
  let _ := E.addCommGroup
  let _ := E.free
  let _ := E.finite
  let _ := E.grpB
  have := E.i_hom
  have := E.q_hom
  have hkill : E.i ≫ r ≫ q₁ = 1 := GlobalTheory.T.splitTorus_hom_eq_one_of_no_cocharacter' _ B₁ E.X hno _ inferInstance
  obtain ⟨⟨ψ, -, hψ⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ G E.B B₁ E.q (r ≫ q₁)
    E.q_hom inferInstance E.q_flat E.q_surjective E.q_quasiCompact (fun T x hx => by
      have h := E.isKernel.lift_fst x (toUnit T) hx
      rw [← h, Category.assoc, hkill, MonObj.comp_one])
  have := E.isAbelian.proper
  have : UniversallyClosed (ψ.left ≫ B₁.hom) := by rw [Over.w]; infer_instance
  have : UniversallyClosed ψ.left := .of_comp_of_isSeparated _ B₁.hom
  have := hG₁.2.1
  have : JacobsonSpace G₁.left := LocallyOfFiniteType.jacobsonSpace G₁.hom
  have hZ : IsClosed (q₁.left ⁻¹' Set.range ψ.left) :=
    ψ.left.isClosedMap.isClosed_range.preimage q₁.left.continuous
  let pt : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  have hsub : closedPoints G₁.left ⊆ q₁.left ⁻¹' Set.range ψ.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hsurj (Over.homMk (pointOfClosedPoint (K := k) G₁.hom y hy)
      (pointOfClosedPoint_comp (K := k) G₁.hom y hy))
    have hy' : r.left (x.left pt) = y := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
      exact pointOfClosedPoint_apply (K := k) G₁.hom y hy pt
    refine ⟨E.q.left (x.left pt), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hψ, Over.comp_left, Scheme.Hom.comp_apply, hy']
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  have : Surjective ψ.left := ⟨fun b => by
    obtain ⟨g, rfl⟩ := q₁.left.surjective b
    exact hall (Set.mem_univ g)⟩
  have : UniversallyClosed B₁.hom := .of_comp_surjective ψ.left _
  have : IsProper B₁.hom := {}
  exact ⟨{ X := X, B := B₁, isAbelian := ⟨hc, hsm, this, hgc⟩, q := q₁, q_hom := hq, q_flat := hfl,
           q_surjective := hsu, q_quasiCompact := inferInstance, i := i₁, i_hom := hi,
           isKernel := hker }⟩

end GlobalTheory.SS
