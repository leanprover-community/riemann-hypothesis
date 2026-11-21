import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportSourceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZeroStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitInduct

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

theorem induct_suppSplit : ∀ {D : D7} (V : HSp D) (N : ℕ) (Q : GA D V → Prop), Q 1 → (∀ x y, Q x → Q y → Q (x * y)) →
    (∀ (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∀ x ∈ GfC V, Formalism.L2.Theta.SuppAt e V x → Q x) →
    ∀ g ∈ GfC V, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom V) g : Matrix (Fin V.rank) (Fin V.rank) _) → Q g := by
  classical
  intro D V N Q h1 hmul hloc g hg hs
  obtain ⟨e₀, he1, he2, he3, he4⟩ := hs
  have heS : e₀ = GlobalTheory.LocalApprox.indA D.host.F he2.toFinset := by
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w ∈ he2.toFinset
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_mem _ hw]
      have hne : evalV D.host.F w e₀ ≠ 0 := he2.mem_toFinset.1 hw
      have h := congrArg (evalV D.host.F w) he1
      rw [map_mul] at h
      exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_notMem _ hw]
      by_contra h
      exact hw (he2.mem_toFinset.2 h)
  have hsupp : ∀ i j, GlobalTheory.LocalApprox.idemE D he2.toFinset * (Formalism.L2.Theta.mt V g - 1) i j =
      (Formalism.L2.Theta.mt V g - 1) i j := by
    intro i j
    have e0 : GlobalTheory.LocalApprox.idemE D he2.toFinset = fj D e₀ := (congrArg (fj D) heS).symm
    rw [e0]
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · have h5 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
        have h6 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (show infHom V g = 1 from hg)
        have h7 := congrFun (congrFun h6 i) j
        rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
        refine h7.trans ?_
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5, mul_zero]
    · have h5 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = ((finHom V g).1 - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
        congr 1
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5]
      exact congrFun (congrFun he4 i) j
  have hgS : GlobalTheory.LocalApprox.cutAt V g he2.toFinset = g := by
    refine GlobalTheory.IdemSupport.mt_inj V ?_
    rw [GlobalTheory.LocalApprox.mt_cutAt]
    ext i j
    have h := hsupp i j
    rw [Matrix.sub_apply] at h
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination h
  have hpl : ∀ v, pl D v = GlobalTheory.LocalApprox.idemE D {v} := fun v => by
    show fj D _ = fj D _
    congr 1
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)]
    · rw [evalV_singleV_ne _ v _ hw, GlobalTheory.LocalApprox.evalV_indA_of_notMem _ (Finset.notMem_singleton.2 hw)]
  have hv : ∀ v ∈ he2.toFinset, Q (GlobalTheory.LocalApprox.cutAt V g {v}) := by
    intro v hvS
    have hv' := he3 v (he2.mem_toFinset.1 hvS)
    obtain ⟨e, he⟩ := _root_.GlobalTheory.MovedSplit.exists_splitAt D v hv'.1
    obtain ⟨PP, hP, hco⟩ := _root_.GlobalTheory.IdemPrime.exists_isIdemAt D v e he
    refine hloc e PP hP ?_ _ (GlobalTheory.LocalApprox.cutAt_mem_GfC V g {v}) ?_
    · intro hm
      refine hv'.2 ?_
      rw [← hco, Ideal.mem_comap, map_natCast]
      exact hm
    · intro i j
      rw [he.2.2, hpl v]
      exact GlobalTheory.LocalApprox.cutAt_supp V g {v} i j
  have key : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), s ⊆ he2.toFinset →
      Q (GlobalTheory.LocalApprox.cutAt V g s) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => intro _; rw [GlobalTheory.LocalApprox.cutAt_empty]; exact h1
    | cons v s h ih =>
      intro hsub
      rw [GlobalTheory.LocalApprox.cutAt_cons]
      exact hmul _ _ (hv v (hsub (Finset.mem_cons_self _ _))) (ih ((Finset.subset_cons h).trans hsub))
  rw [← hgS]
  exact key _ subset_rfl

end GlobalTheory.SplitInduct

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_induction_on_splitPlaceSupport : ∀ {D : D7} (V : HSp D) (N : ℕ) (Q : GA D V → Prop), Q 1 → (∀ x y, Q x → Q y → Q (x * y)) →
    (∀ (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∀ x ∈ GfC V, Formalism.L2.Theta.SuppAt e V x → Q x) →
    ∀ g ∈ GfC V, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom V) g : Matrix (Fin V.rank) (Fin V.rank) _) → Q g := by
  atlas_forward_decl GlobalTheory.SplitInduct.induct_suppSplit
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.MovedAlg

theorem suppSplit_algComb : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ), 0 < N → ∀ g ∈ GfC A, ∀ g' ∈ GfC WW,
      GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom A) g : Matrix (Fin A.rank) (Fin A.rank) _) →
      GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom WW) g' : Matrix (Fin WW.rank) (Fin WW.rank) _) →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (g, g') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t N hN g hg g' hg' hs hs'
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) := fun u v hu hv =>
    GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 _ _ u v hu hv
  have hmul : ∀ p q : GA D A × GA D WW, IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t p X.vac) →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t q X.vac) →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (p * q) X.vac) := by
    rintro ⟨x, h⟩ q hp hq
    rw [map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t x h hp hq
  have hone : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t 1 X.vac) := by
    rw [map_one, Module.End.one_apply]
    refine ⟨1, fun _ => 1, fun _ => 0, fun _ => isAlgebraic_one, fun _ => by simp, ?_⟩
    simp [GlobalTheory.SplitScalar.heisO_zero]
  have hW : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, g') X.vac) :=
    GlobalTheory.T.unitary_induction_on_splitPlaceSupport WW N (fun h => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac)) hone
      (fun x y hx hy => by simpa using hmul _ _ hx hy)
      (fun e P hP' hN' x hx hsx => GlobalTheory.T.theta_local_support_idempotent hP hI hL hX t N e P hP' hN' x hx hsx) g' hg' hs'
  have hA : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (g, 1) X.vac) :=
    GlobalTheory.T.unitary_induction_on_splitPlaceSupport A N (fun x => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, 1) X.vac)) hone
      (fun x y hx hy => by simpa using hmul _ _ hx hy)
      (fun e P hP' hN' x hx hsx => GlobalTheory.T.theta_local_support_source hP hI hL hX t N e P hP' hN' x hx hsx) g hg hs
  have := hmul _ _ hA hW
  simp only [Prod.mk_mul_mk, mul_one, one_mul] at this
  exact this

end GlobalTheory.MovedAlg

end
end
