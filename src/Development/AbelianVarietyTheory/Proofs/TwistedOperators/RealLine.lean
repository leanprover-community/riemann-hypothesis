import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodsOnLineOfInvLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefPerEqGenPer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFockSSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastRealAll
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdaptedFrameOrthonormal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefOfNode

section
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RowReal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

def omLiftOfMultilinear
    (Φ : MultilinearMap ℂ (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap ℂ (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) : OM P →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    ((TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ).comp
      (((LinearMap.llcomp ℂ _ _ _ (TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ)).comp
        PiTensorProduct.lift.toLinearMap).comp (PiTensorProduct.lift Φ)))

theorem omLiftOfMultilinear_tprod
    (Φ : MultilinearMap ℂ (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap ℂ (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) (x y v φ) :
    omLiftOfMultilinear P Φ (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) =
      Φ x y v φ := by
  simp only [omLiftOfMultilinear, TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.uncurry_apply,
    LinearMap.llcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]

theorem invFun_of_multilinear : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)
    (Φ : MultilinearMap ℂ (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap ℂ (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ)))
    (hΦ : ∀ g x y v φ, Φ (fun j => rowFock P j g (x j)) (fun i => colFock P i g (y i)) (psiRep P g v)
      ((baseRep P).dual g φ) = Φ x y v φ), ∃ l ∈ invFun (omRep P), ∀ x y v φ,
      l (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) = Φ x y v φ := by
  intro ι _ _ S P Φ hΦ
  refine ⟨omLiftOfMultilinear P Φ, ?_, omLiftOfMultilinear_tprod P Φ⟩
  intro g z
  have key : (omLiftOfMultilinear P Φ).comp (omRep P g) = omLiftOfMultilinear P Φ := by
    ext x y v φ
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.restrictScalars_apply]
    rw [omRep, Representation.tprod_apply, TensorProduct.map_tmul, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
    simp only [piTprod, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod,
      Pi.monoidHom_apply, omLiftOfMultilinear_tprod]
    exact hΦ g x y v φ
  exact LinearMap.congr_fun key z

end GlobalTheory.RowReal

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

theorem left_cast {D : D7} {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
      φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact hφ

theorem gen_left : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch =>
    (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
    ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  refine ⟨fun a ξ γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g, fun t y η => ?_⟩
  have hm := hS.core.models
  exact left_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
    (fun γ hγ g => congrArg η
      (GlobalTheory.ThetaProjEquiv.ext_left R.cX ((R.HX t).e y) _ _ ((hm.HX t).2.1.le ⟨y, rfl⟩) γ hγ g))

end GlobalTheory.RowReal

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Lin

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem kerA_col_add (t : T) (j : ℕ) (f f' : Sch G (.col t j)) :
    ∀ g h, W.kerA (.col t j) (f + f') g h = W.kerA (.col t j) f g h + W.kerA (.col t j) f' g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_add, Pi.add_apply]

theorem kerA_col_smul (t : T) (j : ℕ) (c : ℂ) (f : Sch G (.col t j)) :
    ∀ g h, W.kerA (.col t j) (c • f) g h = c * W.kerA (.col t j) f g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem kerA_right_add (i j : ℕ) (f f' : Sch G (.right i j)) :
    ∀ g h, W.kerA (.right i j) (f + f') g h = W.kerA (.right i j) f g h + W.kerA (.right i j) f' g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_add, Pi.add_apply]

theorem kerA_right_smul (i j : ℕ) (c : ℂ) (f : Sch G (.right i j)) :
    ∀ g h, W.kerA (.right i j) (c • f) g h = c * W.kerA (.right i j) f g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

end Lin

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Lin2

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem liftA_datum_add {a : Arrow T} {f f' f'' : Sch G a} {F : Fn G a.src}
    (hk : ∀ g h, W.kerA a f'' g h = W.kerA a f g h + W.kerA a f' g h)
    (h1 : LiftConv W M a f F) (h2 : LiftConv W M a f' F) :
    liftA W M a f'' F = liftA W M a f F + liftA W M a f' F := by
  funext x
  simp only [liftA_apply, Pi.add_apply, hk, add_mul]
  exact integral_add (h1 x) (h2 x)

theorem liftA_datum_smul {a : Arrow T} {f f'' : Sch G a} {F : Fn G a.src} (c : ℂ)
    (hk : ∀ g h, W.kerA a f'' g h = c * W.kerA a f g h) :
    liftA W M a f'' F = c • liftA W M a f F := by
  funext x
  simp only [liftA_apply, Pi.smul_apply, smul_eq_mul, hk, mul_assoc, integral_const_mul]

theorem pathLift_column_add (t : T) : ∀ (n : ℕ) (f f' f'' : ∀ j : Fin n, Sch G (.col t j)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j ∧ f' j = f'' j) → f'' j0 = f j0 + f' j0 → ∀ F : Fn G (.top 0),
    PathConv W M (colPath t n) (colFam t n f) F → PathConv W M (colPath t n) (colFam t n f') F →
    liftP W M (colPath t n) (colFam t n f'') F =
      liftP W M (colPath t n) (colFam t n f) F + liftP W M (colPath t n) (colFam t n f') F
  | 0, _, _, _, j0, _, _, _, _, _ => j0.elim0
  | n + 1, f, f', f'', j0, hne, h0, F, h1, h2 => by
    have h1a : PathConv W M (colPath t n) (colFam t n fun j => f j.castSucc) F := h1.1
    have h2a : PathConv W M (colPath t n) (colFam t n fun j => f' j.castSucc) F := h2.1
    have h1b : LiftConv W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F) := h1.2
    have h2b : LiftConv W M (.col t n) (f' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) F) := h2.2
    change liftA W M (.col t n) (f'' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f'' j.castSucc) F) =
      liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F) +
      liftA W M (.col t n) (f' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).1
      have e2 : (fun j : Fin n => f' j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).2
      rw [e1] at h1b ⊢
      rw [e2] at h2b ⊢
      exact liftA_datum_add W M (fun g h => by rw [h0]; exact kerA_col_add W t n _ _ g h) h1b h2b
    · obtain ⟨j1, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      have el : f (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).1
      have el' : f' (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).2
      have ih := pathLift_column_add t n (fun j => f j.castSucc) (fun j => f' j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F h1a h2a
      rw [el] at h1b ⊢
      rw [el'] at h2b ⊢
      rw [ih]
      exact liftA_add W M h1b h2b

theorem pathLift_column_smul (t : T) (c : ℂ) : ∀ (n : ℕ) (f f'' : ∀ j : Fin n, Sch G (.col t j)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j) → f'' j0 = c • f j0 → ∀ F : Fn G (.top 0),
    liftP W M (colPath t n) (colFam t n f'') F = c • liftP W M (colPath t n) (colFam t n f) F
  | 0, _, _, j0, _, _, _ => j0.elim0
  | n + 1, f, f'', j0, hne, h0, F => by
    change liftA W M (.col t n) (f'' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f'' j.castSucc) F) =
      c • liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => hne _ (Fin.castSucc_lt_last j).ne
      rw [e1]
      exact liftA_datum_smul W M c (fun g h => by rw [h0]; exact kerA_col_smul W t n c _ g h)
    · obtain ⟨j1, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      have el : f (Fin.last n) = f'' (Fin.last n) := hne _ (Ne.symm hj)
      have ih := pathLift_column_smul t c n (fun j => f j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F
      rw [el, ih]
      exact liftA_smul W M _ _ c _

theorem pathLift_row_add (k : ℕ) : ∀ (n : ℕ) (f f' f'' : ∀ i : Fin n, Sch G (.right i k)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j ∧ f' j = f'' j) → f'' j0 = f j0 + f' j0 → ∀ F : Fn G (.grid 0 k),
    PathConv W M (rowPath T k n) (rowFam k n f) F → PathConv W M (rowPath T k n) (rowFam k n f') F →
    liftP W M (rowPath T k n) (rowFam k n f'') F =
      liftP W M (rowPath T k n) (rowFam k n f) F + liftP W M (rowPath T k n) (rowFam k n f') F
  | 0, _, _, _, j0, _, _, _, _, _ => j0.elim0
  | n + 1, f, f', f'', j0, hne, h0, F, h1, h2 => by
    have h1a : PathConv W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F := h1.1
    have h2a : PathConv W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F := h2.1
    have h1b : LiftConv W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F) := h1.2
    have h2b : LiftConv W M (.right n k) (f' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F) := h2.2
    change liftA W M (.right n k) (f'' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f'' j.castSucc) F) =
      liftA W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F) +
      liftA W M (.right n k) (f' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).1
      have e2 : (fun j : Fin n => f' j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).2
      rw [e1] at h1b ⊢
      rw [e2] at h2b ⊢
      exact liftA_datum_add W M (fun g h => by rw [h0]; exact kerA_right_add W n k _ _ g h) h1b h2b
    · obtain ⟨j1, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      have el : f (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).1
      have el' : f' (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).2
      have ih := pathLift_row_add k n (fun j => f j.castSucc) (fun j => f' j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F h1a h2a
      rw [el] at h1b ⊢
      rw [el'] at h2b ⊢
      rw [ih]
      exact liftA_add W M h1b h2b

theorem pathLift_row_smul (k : ℕ) (c : ℂ) : ∀ (n : ℕ) (f f'' : ∀ i : Fin n, Sch G (.right i k)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j) → f'' j0 = c • f j0 → ∀ F : Fn G (.grid 0 k),
    liftP W M (rowPath T k n) (rowFam k n f'') F = c • liftP W M (rowPath T k n) (rowFam k n f) F
  | 0, _, _, j0, _, _, _ => j0.elim0
  | n + 1, f, f'', j0, hne, h0, F => by
    change liftA W M (.right n k) (f'' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f'' j.castSucc) F) =
      c • liftA W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => hne _ (Fin.castSucc_lt_last j).ne
      rw [e1]
      exact liftA_datum_smul W M c (fun g h => by rw [h0]; exact kerA_right_smul W n k c _ g h)
    · obtain ⟨j1, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      have el : f (Fin.last n) = f'' (Fin.last n) := hne _ (Ne.symm hj)
      have ih := pathLift_row_smul k c n (fun j => f j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F
      rw [el, ih]
      exact liftA_smul W M _ _ c _

end Lin2

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Outer

variable {X : Type} [MeasurableSpace X] {μ : Measure X} {s : Set X}

end Outer

section Multi

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
  (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)

def colLift (Q1 : PolCol ch.G) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) : Fn ch.G (.top D.R.m) :=
  liftP ch.W M (colPath t D.R.m)
    (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
    (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a))

def rowLift (Q2 : PolRow ch.G) (η : Module.Dual ℂ R.cX.W) : Fn ch.G (.grid D.R.m D.R.m) :=
  liftP ch.W M (rowPath T D.R.m D.R.m)
    (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i))
    (formGen ch t y η)

theorem genPer_eq (Q : PolCol ch.G × PolRow ch.G) ξ η :
    genPer ch t a M d y Q ξ η = ∫ h in M.fd (.grid D.R.m D.R.m),
      colLift ch t a M d Q.1 ξ (stabilizerEmbedding ch.G.sp.topDec h) * rowLift ch t M d y Q.2 η h ∂M.ν (.grid D.R.m D.R.m) := rfl

theorem genConv_int {Q : PolCol ch.G × PolRow ch.G} {ξ η} (h : GenConv ch t a M d y Q ξ η) :
    IntegrableOn (fun h => colLift ch t a M d Q.1 ξ (stabilizerEmbedding ch.G.sp.topDec h) * rowLift ch t M d y Q.2 η h)
      (M.fd (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)) := h.2.2

theorem colLift_add [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ
    (h1 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)))
    (h2 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x' j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a))) :
    colLift ch t a M d (Function.update Q1 i (x + x')) ξ =
      colLift ch t a M d (Function.update Q1 i x) ξ + colLift ch t a M d (Function.update Q1 i x') ξ :=
  pathLift_column_add ch.W M t D.R.m
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x' j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i (x + x') j)) i
    (fun j hj => by simp only [Function.update_of_ne hj, and_self])
    (by simp only [Function.update_self, map_add]) _ h1 h2

theorem colLift_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ :
    colLift ch t a M d (Function.update Q1 i (c • x)) ξ = c • colLift ch t a M d (Function.update Q1 i x) ξ :=
  pathLift_column_smul ch.W M t c D.R.m
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i (c • x) j)) i
    (fun j hj => by simp only [Function.update_of_ne hj])
    (by simp only [Function.update_self, map_smul]) _

theorem rowLift_add [DecidableEq (Fin D.R.m)] (Q2 : PolRow ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) η
    (h1 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
      (formGen ch t y η))
    (h2 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x' j))
      (formGen ch t y η)) :
    rowLift ch t M d y (Function.update Q2 i (x + x')) η =
      rowLift ch t M d y (Function.update Q2 i x) η + rowLift ch t M d y (Function.update Q2 i x') η :=
  pathLift_row_add ch.W M D.R.m D.R.m
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x' j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i (x + x') j)) i
    (fun j hj => by simp only [Function.update_of_ne hj, and_self])
    (by simp only [Function.update_self, map_add]) _ h1 h2

theorem rowLift_smul [DecidableEq (Fin D.R.m)] (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) η :
    rowLift ch t M d y (Function.update Q2 i (c • x)) η = c • rowLift ch t M d y (Function.update Q2 i x) η :=
  pathLift_row_smul ch.W M D.R.m c D.R.m
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i (c • x) j)) i
    (fun j hj => by simp only [Function.update_of_ne hj])
    (by simp only [Function.update_self, map_smul]) _

theorem colLift_xi_add (Q1 : PolCol ch.G) ξ ξ'
    (h1 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)))
    (h2 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ' (ch.col a))) :
    colLift ch t a M d Q1 (ξ + ξ') = colLift ch t a M d Q1 ξ + colLift ch t a M d Q1 ξ' := by
  have hp : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ + ξ') (ch.col a) =
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) + pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ' (ch.col a) := by
    funext h
    simp only [pairVec_apply, LinearMap.add_apply, Pi.add_apply]
  unfold colLift
  rw [hp]
  exact pathLift_add ch.W M _ _ h1 h2

theorem colLift_xi_smul (Q1 : PolCol ch.G) (c : ℂ) ξ :
    colLift ch t a M d Q1 (c • ξ) = c • colLift ch t a M d Q1 ξ := by
  have hp : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (c • ξ) (ch.col a) =
      c • pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) := by
    funext h
    simp only [pairVec_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  unfold colLift
  rw [hp]
  exact pathLift_smul ch.W M _ _ _ _

theorem formGen_add (η η' : Module.Dual ℂ R.cX.W) : formGen ch t y (η + η') = formGen ch t y η + formGen ch t y η' := by
  funext g
  simp only [formGen, LinearMap.add_apply, Pi.add_apply]

theorem formGen_smul (c : ℂ) (η : Module.Dual ℂ R.cX.W) : formGen ch t y (c • η) = c • formGen ch t y η := by
  funext g
  simp only [formGen, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]

theorem rowLift_eta_add (Q2 : PolRow ch.G) η η'
    (h1 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i)) (formGen ch t y η))
    (h2 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i)) (formGen ch t y η')) :
    rowLift ch t M d y Q2 (η + η') = rowLift ch t M d y Q2 η + rowLift ch t M d y Q2 η' := by
  unfold rowLift
  rw [formGen_add]
  exact pathLift_add ch.W M _ _ h1 h2

theorem rowLift_eta_smul (Q2 : PolRow ch.G) (c : ℂ) η :
    rowLift ch t M d y Q2 (c • η) = c • rowLift ch t M d y Q2 η := by
  unfold rowLift
  rw [formGen_smul]
  exact pathLift_smul ch.W M _ _ _ _

end Multi

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Multi2

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
  (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)

theorem genPer_col_add [DecidableEq (Fin D.R.m)] (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q1 : PolCol ch.G)
    (Q2 : PolRow ch.G) (i : Fin D.R.m) (x x' : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ η :
    genPer ch t a M d y (Function.update Q1 i (x + x'), Q2) ξ η =
      genPer ch t a M d y (Function.update Q1 i x, Q2) ξ η + genPer ch t a M d y (Function.update Q1 i x', Q2) ξ η := by
  have i1 := genConv_int ch t a M d y (hc (Function.update Q1 i x, Q2) ξ η)
  have i2 := genConv_int ch t a M d y (hc (Function.update Q1 i x', Q2) ξ η)
  have e := colLift_add ch t a M d Q1 i x x' ξ (hc (Function.update Q1 i x, Q2) ξ η).1
    (hc (Function.update Q1 i x', Q2) ξ η).1
  dsimp only at i1 i2
  rw [genPer_eq, genPer_eq, genPer_eq]
  dsimp only
  rw [e]
  simp only [Pi.add_apply, add_mul]
  exact integral_add i1 i2

theorem genPer_col_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ η :
    genPer ch t a M d y (Function.update Q1 i (c • x), Q2) ξ η = c * genPer ch t a M d y (Function.update Q1 i x, Q2) ξ η := by
  rw [genPer_eq, genPer_eq]
  dsimp only
  rw [colLift_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem genPer_row_add [DecidableEq (Fin D.R.m)] (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q1 : PolCol ch.G)
    (Q2 : PolRow ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) ξ η :
    genPer ch t a M d y (Q1, Function.update Q2 i (x + x')) ξ η =
      genPer ch t a M d y (Q1, Function.update Q2 i x) ξ η + genPer ch t a M d y (Q1, Function.update Q2 i x') ξ η := by
  have i1 := genConv_int ch t a M d y (hc (Q1, Function.update Q2 i x) ξ η)
  have i2 := genConv_int ch t a M d y (hc (Q1, Function.update Q2 i x') ξ η)
  have e := rowLift_add ch t M d y Q2 i x x' η (hc (Q1, Function.update Q2 i x) ξ η).2.1
    (hc (Q1, Function.update Q2 i x') ξ η).2.1
  dsimp only at i1 i2
  rw [genPer_eq, genPer_eq, genPer_eq]
  dsimp only
  rw [e]
  simp only [Pi.add_apply, mul_add]
  exact integral_add i1 i2

theorem genPer_row_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) ξ η :
    genPer ch t a M d y (Q1, Function.update Q2 i (c • x)) ξ η = c * genPer ch t a M d y (Q1, Function.update Q2 i x) ξ η := by
  rw [genPer_eq, genPer_eq]
  dsimp only
  rw [rowLift_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem genPer_xi_add (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q : PolCol ch.G × PolRow ch.G) ξ ξ' η :
    genPer ch t a M d y Q (ξ + ξ') η = genPer ch t a M d y Q ξ η + genPer ch t a M d y Q ξ' η := by
  have i1 := genConv_int ch t a M d y (hc Q ξ η)
  have i2 := genConv_int ch t a M d y (hc Q ξ' η)
  rw [genPer_eq, genPer_eq, genPer_eq, colLift_xi_add ch t a M d Q.1 ξ ξ' (hc Q ξ η).1 (hc Q ξ' η).1]
  simp only [Pi.add_apply, add_mul]
  exact integral_add i1 i2

theorem genPer_xi_smul (Q : PolCol ch.G × PolRow ch.G) (c : ℂ) ξ η :
    genPer ch t a M d y Q (c • ξ) η = c * genPer ch t a M d y Q ξ η := by
  rw [genPer_eq, genPer_eq, colLift_xi_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem genPer_eta_add (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q : PolCol ch.G × PolRow ch.G) ξ η η' :
    genPer ch t a M d y Q ξ (η + η') = genPer ch t a M d y Q ξ η + genPer ch t a M d y Q ξ η' := by
  have i1 := genConv_int ch t a M d y (hc Q ξ η)
  have i2 := genConv_int ch t a M d y (hc Q ξ η')
  rw [genPer_eq, genPer_eq, genPer_eq, rowLift_eta_add ch t M d y Q.2 η η' (hc Q ξ η).2.1 (hc Q ξ η').2.1]
  simp only [Pi.add_apply, mul_add]
  exact integral_add i1 i2

theorem genPer_eta_smul (Q : PolCol ch.G × PolRow ch.G) (c : ℂ) ξ η :
    genPer ch t a M d y Q ξ (c • η) = c * genPer ch t a M d y Q ξ η := by
  rw [genPer_eq, genPer_eq, rowLift_eta_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem genPer_multilinear (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) :
    ∃ Φ : MultilinearMap ℂ (fun j : Fin D.R.m => PolF D (ch.G.V (.top ((j : ℕ) + 1))).rank (ch.G.V (.top j)).rank)
      (MultilinearMap ℂ (fun i : Fin D.R.m => PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank)
        (Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W →ₗ[ℂ] Module.Dual ℂ R.cX.W →ₗ[ℂ] ℂ)),
      ∀ Q ξ η, Φ Q.1 Q.2 ξ η = genPer ch t a M d y Q ξ η := by
  refine ⟨
    { toFun := fun Q1 =>
        { toFun := fun Q2 => LinearMap.mk₂ ℂ (fun ξ η => genPer ch t a M d y (Q1, Q2) ξ η)
            (fun ξ ξ' η => genPer_xi_add ch t a M d y hc _ ξ ξ' η)
            (fun c ξ η => genPer_xi_smul ch t a M d y _ c ξ η)
            (fun ξ η η' => genPer_eta_add ch t a M d y hc _ ξ η η')
            (fun c ξ η => genPer_eta_smul ch t a M d y _ c ξ η)
          map_update_add' := fun Q2 i x x' => LinearMap.ext fun ξ => LinearMap.ext fun η =>
            genPer_row_add ch t a M d y hc Q1 Q2 i x x' ξ η
          map_update_smul' := fun Q2 i c x => LinearMap.ext fun ξ => LinearMap.ext fun η =>
            genPer_row_smul ch t a M d y Q1 Q2 i c x ξ η }
      map_update_add' := fun Q1 i x x' => MultilinearMap.ext fun Q2 => LinearMap.ext fun ξ => LinearMap.ext fun η =>
        genPer_col_add ch t a M d y hc Q1 Q2 i x x' ξ η
      map_update_smul' := fun Q1 i c x => MultilinearMap.ext fun Q2 => LinearMap.ext fun ξ => LinearMap.ext fun η =>
        genPer_col_smul ch t a M d y Q1 Q2 i c x ξ η }, fun Q ξ η => rfl⟩

end Multi2

end GlobalTheory.RowReal
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

theorem setIntegral_fd_mul_right : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {X : Node} (M : Vol G)
    {K : Subgroup (GL (Fin (G.V X).rank) (Formalism.IndefR.Lev.EAf D))}, M.IsAt X K → ∀ (k : GA D (G.V X)),
    MeasurePreserving (fun g : GA D (G.V X) => g * k) (M.ν X) (M.ν X) → Measurable (fun g : GA D (G.V X) => g * k⁻¹) →
    ∀ φ : GA D (G.V X) → ℂ, (∀ γ ∈ GQ (G.V X), ∀ g, φ (γ * g) = φ g) →
    ∫ g in M.fd X, φ (g * k) ∂M.ν X = ∫ g in M.fd X, φ g ∂M.ν X := by
  intro D T L sc G X M K hM k hk hk' φ hφ
  obtain ⟨hH, hF⟩ := hM.haar_fund
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (G.V X).gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig (G.V X).gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig (G.V X).gram
  haveI : Countable (GQ (G.V X)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (G.V X).gram
  haveI := hH
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ (G.V X))
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ (G.V X)) (M.ν X)

  let e : GA D (G.V X) ≃ᵐ GA D (G.V X) :=
    { toFun := fun g => g * k, invFun := fun g => g * k⁻¹,
      left_inv := fun g => by simp, right_inv := fun g => by simp,
      measurable_toFun := hk.measurable, measurable_invFun := hk' }

  have hF' : IsFundamentalDomain (GQ (G.V X)) ((fun g : GA D (G.V X) => g * k) ⁻¹' M.fd X) (M.ν X) :=
    hF.preimage_of_equiv hk.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
  rw [hF.setIntegral_eq hF' (f := fun g => φ (g * k)) (fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hφ γ γ.2 _)]
  exact hk.setIntegral_preimage_emb e.measurableEmbedding φ (M.fd X)

end GlobalTheory.RowReal
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Move

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem integral_ker_move (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    {K : Subgroup (GL (Fin (G.V p.small).rank) (Lev.EAf D))} (hM : M.IsAt p.small K)
    (k : GA D (G.V p.small)) (k' : GA D (G.V p.big))
    (hk : MeasurePreserving (fun g : GA D (G.V p.small) => g * k) (M.ν p.small) (M.ν p.small))
    (hk' : Measurable fun g : GA D (G.V p.small) => g * k⁻¹)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (hF : ∀ γ ∈ GQ (G.V p.small), ∀ g, F (γ * g) = F g) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (h * k') * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p (W.om p (G.toPair p k k') f) g h * F (g * k) ∂M.ν p.small := by
  rw [← setIntegral_fd_mul_right M hM k hk hk' (fun g => W.ker p f g (h * k') * F g) ?_]
  · congr 1
    funext g
    rw [ker_mul]
  · intro γ hγ g
    have e := ker_rat_left W p hp f hf γ hγ 1 (one_mem _) g (h * k')
    rw [one_mul] at e
    simp only [e, hF γ hγ g]

theorem integral_ker_left (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (γ : GA D (G.V p.big)) (hγ : γ ∈ GQ (G.V p.big)) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (γ * h) * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p f g h * F g ∂M.ν p.small := by
  congr 1
  funext g
  have e := ker_rat_left W p hp f hf 1 (one_mem _) γ hγ g h
  rw [one_mul] at e
  rw [e]

end Move

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Paths

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem pathLift_column_leftInvariant (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ γ ∈ GQ (G.V (.top n)), ∀ h,
      liftP W M (colPath t n) (colFam t n f) φ (γ * h) = liftP W M (colPath t n) (colFam t n f) φ h
  | 0, _, _, _, _, hφ, γ, hγ, h => hφ γ hγ h
  | n + 1, hn, f, hf, φ, _, γ, hγ, h => by
    show liftA W M (.col t n) (f (Fin.last n)) _ (γ * h) = liftA W M (.col t n) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.top t n) hn _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_row_leftInvariant (W : G.Weil) (M : Vol G) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ γ ∈ GQ (G.V (.grid n D.R.m)), ∀ h,
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (γ * h) = liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F h
  | 0, _, _, _, _, hF, γ, hγ, h => hF γ hγ h
  | n + 1, hn, f, hf, F, _, γ, hγ, h => by
    show liftA W M (.right n D.R.m) (f (Fin.last n)) _ (γ * h) = liftA W M (.right n D.R.m) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.chi n D.R.m) ⟨hn, le_rfl⟩ _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_column_translate (W : G.Weil) (M : Vol G) (t : T) (κ : ∀ n : ℕ, GA D (G.V (.top n))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ j, j < n → (∃ K, M.IsAt (.top j) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.top j)) => g * κ j) (M.ν (.top j)) (M.ν (.top j)) ∧
      Measurable (fun g : GA D (G.V (.top j)) => g * (κ j)⁻¹)) →
    ∀ (f f' : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    (∀ j : Fin n, W.om (.top t j) (G.toPair (.top t j) (κ j) (κ (j + 1))) (f j) = f' j) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ h, liftP W M (colPath t n) (colFam t n f) φ (h * κ n) =
      liftP W M (colPath t n) (colFam t n f') (fun x => φ (x * κ 0)) h
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | n + 1, hn, hκ, f, f', hf, hff, φ, hφ, h => by
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) φ) (h * κ (n + 1)) =
      liftA W M (.col t n) (f' (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) (fun x => φ (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.top t n) hn hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_column_leftInvariant W M t n (by omega) _ (fun j => hf j.castSucc) φ hφ) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [pathLift_column_translate W M t κ n (by omega) (fun j hj => hκ j (by omega)) _ _ (fun j => hf j.castSucc)
      (fun j => hff j.castSucc) φ hφ g]
    rfl

theorem pathLift_row_translate (W : G.Weil) (M : Vol G) (κ : ∀ n : ℕ, GA D (G.V (.grid n D.R.m))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ i, i < n → (∃ K, M.IsAt (.grid i D.R.m) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.grid i D.R.m)) => g * κ i) (M.ν (.grid i D.R.m)) (M.ν (.grid i D.R.m)) ∧
      Measurable (fun g : GA D (G.V (.grid i D.R.m)) => g * (κ i)⁻¹)) →
    ∀ (f f' : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    (∀ i : Fin n, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (κ i) (κ (i + 1))) (f i) = f' i) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ h, liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (h * κ n) =
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f') (fun x => F (x * κ 0)) h
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | n + 1, hn, hκ, f, f', hf, hff, F, hF, h => by
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F)
        (h * κ (n + 1)) =
      liftA W M (.right n D.R.m) (f' (Fin.last n))
        (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f' i.castSucc) (fun x => F (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.chi n D.R.m) ⟨hn, le_rfl⟩ hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_row_leftInvariant W M n (by omega) _ (fun i => hf i.castSucc) F hF) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [pathLift_row_translate W M κ n (by omega) (fun i hi => hκ i (by omega)) _ _ (fun i => hf i.castSucc)
      (fun i => hff i.castSucc) F hF g]
    rfl

end Paths

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Coef

variable {D : D7}

theorem pairVec_mul_real {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {k : GA D V}
    (hk : k ∈ GinfC V) (x : GA D V) :
    pairVec c (ξ ∘ₗ c.ρ k⁻¹) Ψ x = pairVec c ξ Ψ (x * k) := by
  have e : (finHom V).rangeRestrict (x * k) = (finHom V).rangeRestrict x := by
    have hk1 : (finHom V).rangeRestrict k = 1 := Subtype.ext (by simpa using MonoidHom.mem_ker.1 hk)
    rw [map_mul, hk1, mul_one]
  have h3 : c.ρ (x * k)⁻¹ = c.ρ k⁻¹ * c.ρ x⁻¹ := (congrArg c.ρ (mul_inv_rev x k)).trans (c.ρ.map_mul _ _)
  show ξ (c.ρ k⁻¹ (c.ρ x⁻¹ (Ψ ((finHom V).rangeRestrict x)))) =
    ξ (c.ρ (x * k)⁻¹ (Ψ ((finHom V).rangeRestrict (x * k))))
  exact (congrArg (fun A : Module.End ℂ c.W => ξ (A (Ψ ((finHom V).rangeRestrict x)))) h3.symm).trans
    (congrArg (fun z => ξ (c.ρ (x * k)⁻¹ (Ψ z))) e.symm)

theorem ext_cast_mul_real {X Y : LSp D} (e : X = Y) (c : CoefA Y.sp) (v : Bridge.Gf Y.sp → c.W) (η : Module.Dual ℂ c.W)
    {k : GA D X.sp} (hk : k ∈ GinfC X.sp) (g : GA D X.sp) :
    (η ∘ₗ c.ρ (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) k)⁻¹) (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g)) =
      η (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) (g * k))) := by
  subst e
  exact pairVec_mul_real c η v hk g

end Coef

section Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem formGen_mul_real (t : T) (y : (R.HX t).H) (η : Module.Dual ℂ R.cX.W) {k : GA D (ch.G.V (.grid 0 D.R.m))}
    (hk : k ∈ GinfC (ch.G.V (.grid 0 D.R.m))) (g : GA D (ch.G.V (.grid 0 D.R.m))) :
    formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) k)⁻¹) g =
      formGen ch t y η (g * k) :=
  ext_cast_mul_real (colY_m R.toLevCh) R.cX _ η hk g

end Gen

end GlobalTheory.RowReal
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Outer

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_move (M : Vol G) {K : Subgroup (GL (Fin (G.V (.grid D.R.m D.R.m)).rank) (Lev.EAf D))}
    (hK : M.IsAt (.grid D.R.m D.R.m) K) (k : GA D (G.V (.grid D.R.m D.R.m))) (k' : GA D (G.V (.top D.R.m)))
    (hk : MeasurePreserving (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k) (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)))
    (hk' : Measurable (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k⁻¹))
    (ι : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top D.R.m)))
    (hι : ∀ h, ι h * k' = ι (h * k))
    (P P' : Fn G (.top D.R.m)) (S S' : Fn G (.grid D.R.m D.R.m))
    (hP : ∀ h, P (h * k') = P' h) (hS : ∀ h, S (h * k) = S' h)
    (hPl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, P (ι (γ * h)) = P (ι h))
    (hSl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, S (γ * h) = S h) :
    ∫ h in M.fd (.grid D.R.m D.R.m), P' (ι h) * S' h ∂M.ν (.grid D.R.m D.R.m) =
      ∫ h in M.fd (.grid D.R.m D.R.m), P (ι h) * S h ∂M.ν (.grid D.R.m D.R.m) := by
  rw [← setIntegral_fd_mul_right M hK k hk hk' (fun h => P (ι h) * S h) ?_]
  · congr 1
    funext h
    rw [← hP, ← hS, hι]
  · intro γ hγ h
    simp only [hPl γ hγ h, hSl γ hγ h]

end Outer

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem genPer_move (ch : Choice R)
    {μ0 : T} (hL : R.toLevCh.Is μ0) (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)
    (hMr : ∀ j : Fin D.R.m, ∃ K, M.IsAt (.top j) K) (hMc : ∀ i : Fin (D.R.m + 1), ∃ K, M.IsAt (.grid i D.R.m) K)
    (hd1 : ∀ j, ch.S.toGridChoice.Z.HasVec (d.1 j)) (hd2 : ∀ i, ch.S.toGridChoice.Z.HasVec (d.2 i))
    (hξ : ∀ ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g)
    (hη : ∀ η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (g : Gc D.what₂.Tau (rowSizes D)) (Q Q' : PolCol ch.G × PolRow ch.G)
    (h1 : ∀ j : Fin D.R.m, ch.W.om (.top t j) (ch.G.toPair (.top t j) (ptTop ch.W g j) (ptTop ch.W g (j + 1)))
        (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) =
      ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q'.1 j))
    (h2 : ∀ i : Fin D.R.m, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ptGrid ch.W g i) (ptGrid ch.W g (i + 1)))
        (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) =
      ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q'.2 i))
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) :
    genPer ch t a M d y Q' (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹)
      (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      genPer ch t a M d y Q ξ η := by

  have hfc : ∀ (P : PolCol ch.G) (j : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.top t j)) (ch.G.pT (.top t j))
      (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (P j)) := fun P j =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.top t j) j.2 (d.1 j) (hd1 j)).1 (P j)
  have hfr : ∀ (P : PolRow ch.G) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i D.R.m)) (ch.G.pT (.chi i D.R.m))
      (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (P i)) := fun P i =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.chi i D.R.m) ⟨i.2, rfl⟩ (d.2 i) (hd2 i)).1 (P i)

  have hφ' : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a) = fun x => (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (x * ptTop ch.W g 0) :=
    funext (pairVec_mul_real (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (ptTop_mem ch.W g 0))
  have hF' : formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      fun x => (formGen ch t y η) (x * ptGrid ch.W g 0) :=
    funext (formGen_mul_real ch t y η (ptGrid_mem ch.W g 0))

  have hcol := pathLift_column_translate ch.W M t (ptTop ch.W g) D.R.m le_rfl
    (fun j hj => by
      obtain ⟨K, hK⟩ := hMr ⟨j, hj⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptTop_lt ch.W g hj]
      exact kappa_fst_move ch.W g ⟨j, hj⟩ hK)
    _ _ (hfc Q.1) h1 (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ)
  have hrow := pathLift_row_translate ch.W M (ptGrid ch.W g) D.R.m le_rfl
    (fun i hi => by
      obtain ⟨K, hK⟩ := hMc ⟨i, by omega⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptGrid_le ch.W g (by omega : i < D.R.m + 1)]
      exact kappa_snd_move ch.W g ⟨i, by omega⟩ hK)
    _ _ (hfr Q.2) h2 (formGen ch t y η) (hη η)

  have htop : ∀ h, stabilizerEmbedding ch.G.sp.topDec h * ptTop ch.W g D.R.m = stabilizerEmbedding ch.G.sp.topDec (h * ptGrid ch.W g D.R.m) := by
    intro h
    rw [ptTop_m, kappaTop_apply, ptGrid_le ch.W g (Nat.lt_succ_self D.R.m), GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
    rfl

  obtain ⟨K, hK⟩ : ∃ K, M.IsAt (.grid D.R.m D.R.m) K := hMc (Fin.last D.R.m)
  have hmv : MeasurePreserving (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * ptGrid ch.W g D.R.m)
        (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)) ∧
      Measurable (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * (ptGrid ch.W g D.R.m)⁻¹) := by
    rw [ptGrid_le ch.W g (Nat.lt_succ_self D.R.m)]
    exact kappa_snd_move ch.W g (Fin.last D.R.m) hK
  show defPer t ch.S.toGridChoice M Q' d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a))
      (formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹)) =
    defPer t ch.S.toGridChoice M Q d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (formGen ch t y η)
  rw [hφ', hF']
  have hPl := fun (γ : GA D (ch.G.V (.grid D.R.m D.R.m))) (hγ : γ ∈ GQ (ch.G.V (.grid D.R.m D.R.m)))
      (h : GA D (ch.G.V (.grid D.R.m D.R.m))) =>
    (congrArg _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul ch.G.sp.topDec γ h)).trans
      (pathLift_column_leftInvariant ch.W M t D.R.m le_rfl _ (hfc Q.1) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ) _
        (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational ch.G.sp.topDec γ hγ) (stabilizerEmbedding ch.G.sp.topDec h))
  have hSl := pathLift_row_leftInvariant ch.W M D.R.m le_rfl _ (hfr Q.2) (formGen ch t y η) (hη η)
  exact outer_move M hK (ptGrid ch.W g D.R.m) (ptTop ch.W g D.R.m) hmv.1 hmv.2 (stabilizerEmbedding ch.G.sp.topDec) htop _ _ _ _
    hcol hrow hPl hSl

end Main

end GlobalTheory.RowReal
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenConvProof

variable {D : D7}

theorem invCont_cast {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hc : Continuous φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    Continuous (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
        φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact ⟨hc, hl⟩

theorem genPer_conv : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t a, ch.S.SumOK t (ch.Phi a) →
    ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y Q ξ η, GenConv ch t a M d y Q ξ η := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t a hOK β hβ M hM τ hτ d hd y Q ξ η
  have hL := s.core.lev
  have hm := s.core.models
  have hcol : GlobalTheory.DefConv.IsInvCont (.top 0) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) :=
    ⟨GlobalTheory.RowBplus.pairVec_cont ch.G ch.W.θ ch.W.θ_is ξ (col_mem ch a),
      fun γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g⟩
  have hx := (hm.HX t).2.1.le (LinearMap.mem_range_self (R.HX t).e y)
  have hform : GlobalTheory.DefConv.IsInvCont (.grid 0 D.R.m) (formGen ch t y η) := by
    have k := invCont_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
      ((LinearMap.continuous_of_finiteDimensional η).comp
        (GlobalTheory.ThetaIntegrand.ext_continuous R.cX hm.cX R.βX (R.datXt t) hx))
      (fun γ hγ g => by simp only [GlobalTheory.ThetaIntegrand.ext_invariant R.cX hx γ hγ g])
    exact ⟨k.1, k.2⟩
  have hv := hOK.vec β τ hτ d hd
  have hcG : Path.Fam.All (fun a f => GlobalTheory.DefConv.Good ch.W M a f)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) :=
    GlobalTheory.DefConv.all_colFam t _ _ fun j => GlobalTheory.DefConv.good_col ch.W M j.2 _
      (GlobalTheory.DefConv.theta_fock ch.W ch.S.toGridChoice (p := .top t j) (by show (j : ℕ) + 1 ≤ D.R.m; omega)
        (by show (j : ℕ) + 1 ≤ D.R.m; omega) (d.1 j) (hv.1 j) (Q.1 j))
      (GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .top j) (show (j : ℕ) ≤ D.R.m by omega) rfl) (hM.1 j j.2)
  have hrG : Path.Fam.All (fun a f => GlobalTheory.DefConv.Good ch.W M a f)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) :=
    GlobalTheory.DefConv.all_rowFam D.R.m _ _ fun i => GlobalTheory.DefConv.good_row ch.W M i.2 _
      (GlobalTheory.DefConv.theta_fock ch.W ch.S.toGridChoice (p := .chi i D.R.m)
        (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨by omega, rfl⟩)
        (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) (d.2 i) (hv.2 i) (Q.2 i))
      (GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .grid i D.R.m) ⟨by omega, le_rfl⟩ (by simp [Node.neg]))
      (hM.2 i (by omega))
  obtain ⟨hc1, hc2⟩ := GlobalTheory.DefConv.path ch.W M hcol _ _ hcG
  obtain ⟨hr1, hr2⟩ := GlobalTheory.DefConv.path ch.W M hform _ _ hrG
  refine ⟨hc1, hr1, ?_⟩
  obtain ⟨hac, hamul, haQ⟩ := GlobalTheory.T.unitaryEmbedding_continuous_mul_rational ch.G.sp.topDec
  have hpos := GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by simp [Node.neg])
  obtain ⟨Cc, hCc, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.grid D.R.m D.R.m))
  obtain ⟨hH, hfd⟩ := (hM.2 D.R.m le_rfl).haar_fund
  refine GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact _ _ _ Cc hfd hCc hcov _
    ((hc2.1.comp hac).mul hr2.1) fun γ hγ g => ?_
  simp only [hamul, hc2.2 _ (haQ γ hγ), hr2.2 γ hγ]

end GlobalTheory.GenConvProof

end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def pullBil {V₁ V₂ W₁ W₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₁]
    [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (a : V₁ →ₗ[ℂ] W₁) (b : V₂ →ₗ[ℂ] W₂) :
    (W₁ →ₗ[ℂ] W₂ →ₗ[ℂ] ℂ) →ₗ[ℂ] (V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ) where
  toFun f := f.compl₁₂ a b
  map_add' f f' := by ext; simp
  map_smul' c f := by ext; simp

theorem invLine_of_iso [DecidableEq D.what₂.Tau] (ch : Choice R) {μ0 : T} (hL : R.toLevCh.Is μ0)
    (hlf : (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
      ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (hc : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support,
        ∀ y Q ξ η, GenConv ch t a M d y Q ξ η)
    (Aψ : weylSub ((rowSizes D).nR (0 : Fin ((rowSizes D).m + 1))) (psiWt (rowEntries D ch.sc.cGap)) ≃ₗ[ℂ]
      Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W)
    (hA : ∀ g F, Aψ (psiRep (rowEntries D ch.sc.cGap) g F) =
      Aψ F ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ ((kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹)
    (Bf : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
      Module.Dual ℂ R.cX.W)
    (hB : ∀ g φ, Bf ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
      Bf φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹) :
    InvLine ch := by
  classical
  obtain ⟨tc, tr, htr⟩ := GlobalTheory.RowReal.exists_fock_transport hL ch.W
  refine ⟨D.what₂.Tau, inferInstance, inferInstance, rowSizes D, rowEntries D ch.sc.cGap,
    fun τ => rowEntries_good D _ τ, fun Q => PiTensorProduct.tprod ℂ (fun j => tc j (Q.1 j)) ⊗ₜ[ℂ]
      (PiTensorProduct.tprod ℂ (fun i => tr i (Q.2 i)) ⊗ₜ[ℂ] (Aψ.symm ch.ξ ⊗ₜ[ℂ] Bf.symm (R.prX.flip ch.cv.v))), ?_⟩
  intro t a hS β hβ M hM τ hτ d hd y
  obtain ⟨Φ0, hΦ0⟩ := GlobalTheory.RowReal.genPer_multilinear ch t a M d y (hc t a hS β hβ M hM τ hτ d hd y)
  let Irow := (LinearMap.compMultilinearMapₗ ℂ (pullBil Aψ.toLinearMap Bf.toLinearMap)) ∘ₗ
    (MultilinearMap.compLinearMapₗ (fun i : Fin D.R.m => (tr i).symm.toLinearMap))
  let Φ := (Irow.compMultilinearMap Φ0).compLinearMap (fun j : Fin D.R.m => (tc j).symm.toLinearMap)
  have hΦ : ∀ x₁ y₁ v₁ φ₁, Φ x₁ y₁ v₁ φ₁ =
      genPer ch t a M d y (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁) :=
    fun x₁ y₁ v₁ φ₁ => hΦ0 (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁)
  have hv := hS.vec β τ hτ d hd
  have hinv : ∀ g x₁ y₁ v₁ φ₁, Φ (fun j => rowFock (rowEntries D ch.sc.cGap) j g (x₁ j))
      (fun i => colFock (rowEntries D ch.sc.cGap) i g (y₁ i)) (psiRep (rowEntries D ch.sc.cGap) g v₁)
      ((baseRep (rowEntries D ch.sc.cGap)).dual g φ₁) = Φ x₁ y₁ v₁ φ₁ := by
    intro g x₁ y₁ v₁ φ₁
    rw [hΦ, hΦ, hA, hB]
    obtain ⟨h1, h2⟩ := htr ch.S.toGridChoice g t
    have e1 : ptTop ch.W g 0 = (kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩ := ptTop_lt ch.W g _
    have e2 : ptGrid ch.W g 0 = (kappa ch.W g).2 0 := ptGrid_le ch.W g (Nat.succ_pos _)
    have key := GlobalTheory.RowReal.genPer_move ch hL t a M d y (fun j => ⟨_, hM.1 j j.2⟩) (fun i => ⟨_, hM.2 i (Nat.le_of_lt_succ i.2)⟩)
      hv.1 hv.2 (hlf.1 a) (hlf.2 t y) g (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i))
      (fun j => (tc j).symm (rowFock (rowEntries D ch.sc.cGap) j g (x₁ j)),
        fun i => (tr i).symm (colFock (rowEntries D ch.sc.cGap) i g (y₁ i)))
      (fun j => by simpa using h1 j (d.1 j) (hv.1 j) ((tc j).symm (x₁ j)))
      (fun i => by simpa using h2 i (d.2 i) (hv.2 i) ((tr i).symm (y₁ i))) (Aψ v₁) (Bf φ₁)
    rw [e1, e2] at key
    exact key
  obtain ⟨l, hl, hle⟩ := GlobalTheory.RowReal.invFun_of_multilinear (rowEntries D ch.sc.cGap) Φ hinv
  refine ⟨l, hl, fun Q => ?_⟩
  rw [hle]
  refine Eq.trans ?_ (hΦ _ _ _ _).symm
  simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem invLine_big : Big fun ch => InvLine ch := by
  obtain ⟨C1, h1⟩ := GlobalTheory.RowReal.gen_left
  obtain ⟨C2, h2⟩ := GlobalTheory.GenConvProof.genPer_conv
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, h1'⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, h2'⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  classical
  have hlf := h1' D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hc := h2' D large₂ he (le_of_max_le_right hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hL := hS.core.lev
  obtain ⟨Aψ, hA⟩ := GlobalTheory.CoefPsi.coefPsi ch.W (posOnb_of_defNode ch.W A.μ0 hL (X := .top 0) (Nat.zero_le _))
  obtain ⟨Bf, hB⟩ := GlobalTheory.CoefBase.coefBase ch hS.core.models.inf hS.core.models.cX hS.core.models.prX hch.weil
    (posOnb_of_defNode ch.W A.μ0 hL (X := .grid 0 D.R.m) ⟨Nat.zero_le _, rfl⟩)
  exact invLine_of_iso ch hL hlf hc Aψ hA Bf hB

end GlobalTheory.RowReal
end
end

open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_definitePeriods_invariant_functional : Big fun ch => InvLine ch := by
  atlas_forward_decl GlobalTheory.RowReal.invLine_big
end

section
section
open GlobalTheory.RowClaim GlobalTheory.RowReal

theorem GlobalTheory.RowReal.periodsOnLine_big : Big fun ch => PeriodsOnLine ch :=
  big_mono (fun ch h => periodsOnLine_of_invLine GlobalTheory.OneFunctional.oneLine ch h) GlobalTheory.T.rowTest_definitePeriods_invariant_functional
end

open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_realPlaces_definitePeriods_onOneLine : Big fun ch => PeriodsOnLine ch := by
  atlas_forward_decl GlobalTheory.RowReal.periodsOnLine_big
end

section
namespace GlobalTheory.RowReal

open GlobalTheory.RowClaim

theorem realLine : Big fun ch => RealLine ch :=
  big_mono (fun ch h => realLine_of_periodsOnLine ch h) GlobalTheory.T.rowTest_realPlaces_definitePeriods_onOneLine

end GlobalTheory.RowReal
end
