module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAddFinrankOfKernel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisOfFormEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalLincomb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpOnto

theorem exists_sec_comb {X : Scheme.{0}} {L : LB X} {n : ℕ} (r : Fin n → Γ(X, ⊤)) (b : Fin n → LB.Sec L) :
    ∃ t : LB.Sec L, ∀ j, t.f j = ∑ i, resTop _ (r i) * (b i).f j := by
  induction n with
  | zero => exact ⟨DVR.SecOps.secZero, fun j => by simp [DVR.SecOps.secZero]⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (fun i => r i.succ) (fun i => b i.succ)
    refine ⟨DVR.SecOps.secAdd (DVR.SecOps.secScale (r 0) (b 0)) t, fun j => ?_⟩
    rw [Fin.sum_univ_succ, ← ht j]
    rfl

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {K : Type} (S : Finset K) (s : K → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DVR.add_f, ih]

theorem exists_expF_of_fam : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → U.FE F k → ∀ s : Fam D F k, ∃ t, U.ExpF F k t s.s := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB F _ _ k hk hFE s
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow_field hL2.secTwist V A F k hk
  choose e he using fun i => GlobalTheory.T.exists_fourierJacobi_expansion_over_field hL hL2 V hV D A G U F k hk (b i)
  let f : Fin (k ^ A.g) → Fam D F k := fun i => ⟨e i, hFE _ _ (he i)⟩
  have comb : ∀ c : Fin (k ^ A.g) → F, ∃ t, (∀ j, t.f j = ∑ i,
      liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j) ∧
      U.ExpF F k t (∑ i, c i • f i).s := fun c => by
    obtain ⟨t, ht⟩ := exists_sec_comb (fun i => (fst (TFK (R := V) F) A.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b
    refine ⟨t, ht, ExpLinC.expF_lincomb V hV D A G U F k _ c b e t _ he ht fun α j => ?_⟩
    exact fam_sum_f _ _ α j
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨t, ht, hE⟩ := comb c
    obtain ⟨t', ht', hE'⟩ := comb 0
    have h0 : (∑ i, (0 : Fin (k ^ A.g) → F) i • f i) = ∑ i, c i • f i := by
      rw [hc]; simp
    have htt : t = t' := (GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k t t' _ _ hE hE').2 (by rw [h0])
    subst htt
    exact congrFun ((hb t).unique ht ht')
  obtain ⟨hfin, hdim⟩ := finrank_fam_of_laws hL hL2 V D hB F k hk
  have hg : A.g = D.P.g + D.rank := PreU.dim_eq V hV D A G U
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [hdim, Fintype.card_fin, hg])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (hsp ▸ Submodule.mem_top (x := s))
  obtain ⟨t, -, hE⟩ := comb c
  exact ⟨t, hc ▸ hE⟩

end GlobalTheory.UU.ExpOnto

end
