module

public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.CoefCol
public import Formalism.LocalToGlobal.Columns.ColForms
public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
public import Formalism.LocalToGlobal.Columns.ToHLat
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.LocalToGlobal.Columns.AtTOwedC
public import Formalism.LocalToGlobal.Columns.AtTOwedS
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Formalism.LocalToGlobal.Columns.DGamAut
public import Formalism.LocalToGlobal.Columns.SmulMemTrpSet
public import Formalism.LocalToGlobal.Columns.AdjointFrobeniusPreservesRamified
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
public import Formalism.LocalToGlobal.Columns.RowFormsGood
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.HeckeSpCount
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
import Mathlib.RingTheory.PiTensorProduct

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.Columns.DiamondPreservesRamified, Formalism.LocalToGlobal.Columns.Record

-- ===== clump member: Formalism.LocalToGlobal.Columns.DiamondPreservesRamified =====
-- clump-header: {"m": "Formalism.LocalToGlobal.Columns.DiamondPreservesRamified", "h": "module\n\npublic import Formalism.LocalToGlobal.Columns.StdLatUnimodular\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.LocalToGlobal.Columns.CoefCol\npublic import Formalism.LocalToGlobal.Columns.ColForms\npublic import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end Cols

section Adj

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Adj

section AtW

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AtW

end Formalism.L2.Col
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.Columns.DiamondPreservesRamified =====

-- ===== clump member: Formalism.LocalToGlobal.Columns.Record =====
-- clump-header: {"m": "Formalism.LocalToGlobal.Columns.Record", "h": "module\n\npublic import Formalism.LocalToGlobal.Columns.ToHLat\npublic import Formalism.LocalToGlobal.Columns.PolyFn\npublic import Formalism.LocalToGlobal.Columns.AtTOwedC\npublic import Formalism.LocalToGlobal.Columns.AtTOwedS\npublic import Formalism.LocalToGlobal.Columns.RecLevel\npublic import Formalism.LocalToGlobal.Columns.DGamAut\nimport Formalism.LocalToGlobal.Columns.HeckeSpCount\npublic import Formalism.LocalToGlobal.Columns.SmulMemTrpSet\nimport Formalism.LocalToGlobal.Columns.AdelicLemmas\npublic import Formalism.LocalToGlobal.Columns.AdjointFrobeniusPreservesRamified\nimport Formalism.LocalToGlobal.Columns.CoefColLemmas\npublic import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds\npublic import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds\npublic import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds\npublic import Formalism.LocalToGlobal.Columns.DiamondPreservesRamified\nimport Formalism.LocalToGlobal.Columns.PolyFnLemmas\npublic import Formalism.LocalToGlobal.Columns.RowFormsGood\npublic import Formalism.LocalToGlobal.Columns.ToHLatLemmas\nimport Formalism.LocalToGlobal.Divisibility.ClassSumLemmas\nimport Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure Ev (S : GSD K) (σ : K →+* ℂ) where

  Y : Type

  ev : S.V →ₛₗ[σ] (Y → ℂ)
  li : LinearIndependent ℂ fun i => ev (S.bV i)

  ip : (Y → ℂ) →ₗ⋆[ℂ] (Y → ℂ) →ₗ[ℂ] ℂ
  ip_ev : ∀ x y, ip (ev x) (ev y) = σ (S.pair x y)

  tr : S.G →* ((Y → ℂ) ≃ₗ[ℂ] (Y → ℂ))
  tr_ev : ∀ g x, tr g (ev x) = ev (S.ρ g x)

namespace Ev

variable {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

def evCl : (S.Cl → S.V) →ₛₗ[σ] (S.Cl → E.Y → ℂ) where
  toFun f := fun c => E.ev (f c)
  map_add' f g := by funext c; exact map_add E.ev _ _
  map_smul' a f := by funext c; exact LinearMap.map_smulₛₗ E.ev _ _

def emb : S.EqFun →ₛₗ[σ] (S.Cl → E.Y → ℂ) where
  toFun φ := fun c => E.ev ((φ : S.D → S.V) (S.outSec.rep c))
  map_add' φ ψ := by funext c; exact map_add E.ev _ _
  map_smul' a φ := by funext c; exact LinearMap.map_smulₛₗ E.ev _ _

def trPt (d : S.D) : (E.Y → ℂ) ≃ₗ[ℂ] (E.Y → ℂ) := E.tr (S.outSec.mv d)

def atPt (d : S.D) (F : S.Cl → E.Y → ℂ) : E.Y → ℂ := E.trPt d (F (S.cls d))

def opOn (δ : S.D → S.D) : (S.Cl → E.Y → ℂ) →ₗ[ℂ] (S.Cl → E.Y → ℂ) where
  toFun F := fun c => E.atPt (δ (S.outSec.rep c)) F
  map_add' F G := by funext c; exact map_add (E.trPt _) _ _
  map_smul' a F := by funext c; exact map_smul (E.trPt _) _ _

def lin : (S.ιV → ℂ) →ₗ[ℂ] (E.Y → ℂ) := Fintype.linearCombination ℂ fun i => E.ev (S.bV i)

def gram : Matrix S.ιV S.ιV ℂ := Matrix.of fun i j => E.ip (E.ev (S.bV i)) (E.ev (S.bV j))

def ipB : (E.Y → ℂ) →ₗ[ℂ] (S.ιV → ℂ) := LinearMap.pi fun j => E.ip (E.ev (S.bV j))

open Classical in
def co : (E.Y → ℂ) →ₗ[ℂ] (S.ιV → ℂ) :=
  if IsUnit E.gram.det then Matrix.toLin' E.gram⁻¹ ∘ₗ E.ipB
  else (E.lin.exists_leftInverse_of_injective E.lin_ker).choose

def extend {M : Type} [AddCommGroup M] [Module ℂ M] (ℓ : S.V →ₛₗ[σ] M) : (E.Y → ℂ) →ₗ[ℂ] M :=
  (Fintype.linearCombination ℂ fun i => ℓ (S.bV i)) ∘ₗ E.co

def ipCl (h : S.Ok) : (S.Cl → E.Y → ℂ) →ₗ⋆[ℂ] (S.Cl → E.Y → ℂ) →ₗ[ℂ] ℂ :=
  letI := h.fintypeCl
  ∑ c : S.Cl, ((Nat.card (MulAction.stabilizer S.G (S.outSec.rep c)) : ℕ) : ℂ)⁻¹ •
    ((E.ip.comp (LinearMap.proj c)).compl₂ (LinearMap.proj c))

def Fi : Submodule ℂ (S.Cl → E.Y → ℂ) := Submodule.span ℂ (Set.range E.emb)

end Ev

end GSD

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

def evAt {ι : Type} (pts : ι → S.D) : (S.Cl → E.Y → ℂ) →ₗ[ℂ] (ι → E.Y → ℂ) :=
  LinearMap.pi fun i => (E.trPt (pts i)).toLinearMap ∘ₗ LinearMap.proj (S.cls (pts i))

def perCl (h : S.Ok) {ι : Type} [Fintype ι] (ℓ : S.Cl → ι → (S.V →ₛₗ[σ] ℂ)) :
    (S.Cl → E.Y → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ :=
  letI := h.fintypeCl
  LinearMap.mk₂ ℂ (fun F z => ∑ c : S.Cl,
      ((Nat.card (MulAction.stabilizer S.G (S.outSec.rep c)) : ℕ) : ℂ)⁻¹ * ∑ a, z a * E.extend (ℓ c a) (F c))
    (fun F F' z => by simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib])
    (fun a F z => by
      simp only [Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      ring)
    (fun F z z' => by simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib])
    (fun a F z => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      ring)

end GSD.Ev

section Fr

variable {X : Fields} {n : ℕ}

abbrev FrS (X : Fields) (σ₀ : X.K →+* ℂ) (n : ℕ) : Type :=
  Frames (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt σ₀ X.emb))

def frMul (σ₀ : X.K →+* ℂ) (γ : GL (Fin n) X.E) (y : FrS X σ₀ n) : FrS X σ₀ n :=
  ⟨fun τ => atInf (embAt σ₀ X.emb) (γ : Matrix (Fin n) (Fin n) X.E) τ * y.1 τ, fun τ => by
    rw [Matrix.det_mul]
    exact (Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt σ₀ X.emb τ) γ)).mul (y.2 τ)⟩

def frEquiv (σ₀ : X.K →+* ℂ) (γ : GL (Fin n) X.E) : FrS X σ₀ n ≃ FrS X σ₀ n where
  toFun := frMul σ₀ γ
  invFun := frMul σ₀ γ⁻¹
  left_inv y := by rw [← frMul_mul, inv_mul_cancel, frMul_one]
  right_inv y := by rw [← frMul_mul, mul_inv_cancel, frMul_one]

def frSub (σ₀ : X.K →+* ℂ) (γ : GL (Fin n) X.E) : (FrS X σ₀ n → ℂ) ≃ₗ[ℂ] (FrS X σ₀ n → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (frEquiv σ₀ γ⁻¹)

variable {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

def roundEv (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (lam : X.Tau → DomWeight n) (L : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG) :
    (formGSD (roundPk X lam L) Λ).Ev σ₀ where
  Y := FrS X σ₀ n
  ev := evV X.emb 1 lam σ₀
  li := evV_linearIndependent X.emb 1 lam σ₀ (stdFrC _) _ (bVV X.K lam).linearIndependent
  ip := ipFr _ lam (stdFrC _)
  ip_ev x y := ipFr_evV X.emb 1 lam σ₀ (stdFrC _) (fun τ => by simp [stdFrC, gramC]) x y fun m => hσ _
  tr := MonoidHom.mk' (fun g => (frSub σ₀ (ufGL X.E n g.1)).trans
      (LinearEquiv.smulOfUnit (Units.map σ₀.toMonoidHom (Λ.chr g.2)))) (fun g g' => by
    ext f y
    show σ₀ ((Λ.chr (g * g').2 : X.Kˣ) : X.K) • f (frMul σ₀ (ufGL X.E n (g * g').1)⁻¹ y) =
      σ₀ ((Λ.chr g.2 : X.Kˣ) : X.K) • (σ₀ ((Λ.chr g'.2 : X.Kˣ) : X.K) •
        f (frMul σ₀ (ufGL X.E n g'.1)⁻¹ (frMul σ₀ (ufGL X.E n g.1)⁻¹ y)))
    rw [← frMul_mul, ← _root_.mul_inv_rev, Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, Units.val_mul, map_mul, smul_smul])
  tr_ev g x := by
    funext y
    have h2 := evV_rhoVr_tr X.emb 1 lam σ₀ (ufGL X.E n g.1) x y (frMul σ₀ (ufGL X.E n g.1)⁻¹ y) (fun τ => by
      have := congrArg (fun z : FrS X σ₀ n => z.1 τ) (frMul_mul σ₀ (ufGL X.E n g.1) (ufGL X.E n g.1)⁻¹ y)
      simp only [mul_inv_cancel, frMul_one] at this
      exact this)
    have h3 : evV X.emb 1 lam σ₀ (((Λ.chr g.2 : X.Kˣ) : X.K) • rhoVr X.emb lam (ufGL X.E n g.1) x) =
        σ₀ ((Λ.chr g.2 : X.Kˣ) : X.K) • evV X.emb 1 lam σ₀ (rhoVr X.emb lam (ufGL X.E n g.1) x) :=
      LinearMap.map_smulₛₗ _ _ _
    show σ₀ ((Λ.chr g.2 : X.Kˣ) : X.K) • (evV X.emb 1 lam σ₀ x) (frMul σ₀ (ufGL X.E n g.1)⁻¹ y) =
      (evV X.emb 1 lam σ₀ (((Λ.chr g.2 : X.Kˣ) : X.K) • rhoVr X.emb lam (ufGL X.E n g.1) x)) y
    rw [h3, Pi.smul_apply, h2]

end Fr

section ModP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

abbrev modP (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) : Type :=
  ↥M ⧸ (P.asIdeal • (⊤ : Submodule (𝓞 E) ↥M))

def modP.mk (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) : ↥M →ₗ[𝓞 E] modP P M :=
  Submodule.mkQ _

def modP.rep {P : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) (Sp E n)} (x : modP P M) : Sp E n :=
  ((Quotient.out x : ↥M) : Sp E n)

def modP.lift (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (f : ↥M →ₗ[𝓞 E] 𝓞 E ⧸ P.asIdeal) :
    Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M) :=
  LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := P.asIdeal))
    (Submodule.liftQ _ f (by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker, map_smul, quot_smul_def, Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]))

open Classical in
def modP.ext (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : modP P M → 𝓞 E ⧸ P.asIdeal) (y : Sp E n) :
    𝓞 E ⧸ P.asIdeal :=
  if h : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M then
    Ring.inverse (Ideal.Quotient.mk P.asIdeal h.choose) * g (modP.mk P M ⟨h.choose • y, h.choose_spec.2⟩)
  else 0

def gmapEquiv (M : Submodule (𝓞 E) (Sp E n)) (γ : Sp E n ≃ₗ[E] Sp E n) : ↥M ≃ₗ[𝓞 E] ↥(gmap γ M) :=
  (γ.restrictScalars (𝓞 E)).submoduleMap M

def modP.map (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (γ : Sp E n ≃ₗ[E] Sp E n) :
    modP P M ≃ₗ[𝓞 E ⧸ P.asIdeal] modP P (gmap γ M) :=
  LinearEquiv.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := P.asIdeal))
    (Submodule.Quotient.equiv _ _ (gmapEquiv M γ) (by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]))

end ModP

section LevT

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

private theorem rec_deco_full_lattice (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    Submodule.IsFullLattice E d.1.N :=
  hcnt_isFullLattice_of_unimodular d.2.lat d.2.uni

namespace DecoSet

abbrev lv (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) : Type := modP P.1 d.1.N

def fv (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (d.lv P) :=
  modP.lift P.1 d.1.N (d.2.fLin P d.1.N (le_locP _ _))

def upL (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 E) (x : d.lv P) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) := d.up P q (modP.rep x)

abbrev lk (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) : Type := modP P.1 (d.1.kerAt P)

def e1 (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) : Sp E n := d.2.exists_dualBasis.choose P

open Classical in
def te (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 E) : d.lk P :=
  if h : q • d.e1 P ∈ d.1.kerAt P then modP.mk P.1 (d.1.kerAt P) ⟨_, h⟩ else 0

def dnL (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (d.lk P)) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) :=
  d.dn P (modP.ext P.1 (d.1.kerAt P) g)

end DecoSet

end LevT

section MoveLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem modP.mk_osmul (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M))
    (a : 𝓞 E) (x : ↥M) : g (modP.mk P M (a • x)) = Ideal.Quotient.mk P.asIdeal a * g (modP.mk P M x) := by
  have e : a • modP.mk P M x = (Ideal.Quotient.mk P.asIdeal a) • modP.mk P M x :=
    (algebraMap_smul (𝓞 E ⧸ P.asIdeal) a (modP.mk P M x)).symm
  rw [map_smul, e, map_smul, smul_eq_mul]

theorem modP.ext_spec (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M))
    (y : Sp E n) {s : 𝓞 E} (hs : s ∉ P.asIdeal) (hy : s • y ∈ M) :
    Ideal.Quotient.mk P.asIdeal s * modP.ext P M g y = g (modP.mk P M ⟨s • y, hy⟩) := by
  have hex : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M := ⟨s, hs, hy⟩
  unfold modP.ext
  rw [dite_eq_left hex]
  have htP : hex.choose ∉ P.asIdeal := hex.choose_spec.1
  have htM : hex.choose • y ∈ M := hex.choose_spec.2
  have key : Ideal.Quotient.mk P.asIdeal hex.choose * g (modP.mk P M ⟨s • y, hy⟩) =
      Ideal.Quotient.mk P.asIdeal s * g (modP.mk P M ⟨hex.choose • y, htM⟩) := by
    rw [← modP.mk_osmul, ← modP.mk_osmul]
    congr 2
    exact Subtype.ext (smul_comm hex.choose s y)
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hu : IsUnit (Ideal.Quotient.mk P.asIdeal hex.choose) :=
    isUnit_iff_ne_zero.mpr fun h0 => htP (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  calc Ideal.Quotient.mk P.asIdeal s * (Ring.inverse (Ideal.Quotient.mk P.asIdeal hex.choose) *
        g (modP.mk P M ⟨hex.choose • y, htM⟩))
      = Ring.inverse (Ideal.Quotient.mk P.asIdeal hex.choose) *
        (Ideal.Quotient.mk P.asIdeal s * g (modP.mk P M ⟨hex.choose • y, htM⟩)) := by ring
    _ = Ring.inverse (Ideal.Quotient.mk P.asIdeal hex.choose) *
        (Ideal.Quotient.mk P.asIdeal hex.choose * g (modP.mk P M ⟨s • y, hy⟩)) := by rw [key]
    _ = g (modP.mk P M ⟨s • y, hy⟩) := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

theorem modP.ext_of_mem (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M))
    (x : ↥M) : modP.ext P M g x.1 = g (modP.mk P M x) := by
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have h := modP.ext_spec P M g x.1 h1 (by rw [one_smul]; exact x.2)
  rw [map_one, one_mul] at h
  rw [h]
  congr 2
  exact Subtype.ext (one_smul _ _)

theorem modP.ext_funAt (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M)) :
    FunAt P M (modP.ext P M g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨s, hs, hsx⟩ := (mem_locP P M x).1 hx
    obtain ⟨t, ht, hty⟩ := (mem_locP P M y).1 hy
    have hst : s * t ∉ P.asIdeal := fun h => (P.isPrime.mem_or_mem h).elim hs ht
    have h1 : (s * t) • x ∈ M := by rw [mul_comm, mul_smul]; exact M.smul_mem t hsx
    have h2 : (s * t) • y ∈ M := by rw [mul_smul]; exact M.smul_mem s hty
    have h3 : (s * t) • (x + y) ∈ M := by rw [smul_add]; exact M.add_mem h1 h2
    apply mul_left_cancel₀ (mk_ne_zero hst)
    rw [mul_add, modP.ext_spec P M g _ hst h3, modP.ext_spec P M g _ hst h1, modP.ext_spec P M g _ hst h2, ← map_add (f := _), ← map_add (f := _)]
    congr 2
    exact Subtype.ext (smul_add _ _ _)
  · intro a x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locP P M x).1 hx
    have h1 : s • a • x ∈ M := by rw [smul_comm]; exact M.smul_mem a hsx
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [modP.ext_spec P M g _ hs h1, mul_left_comm, modP.ext_spec P M g _ hs hsx, ← modP.mk_osmul]
    congr 2
    exact Subtype.ext (smul_comm _ _ _)
  · intro x hx
    unfold modP.ext
    rw [dite_eq_right fun h => hx ((mem_locP P M x).2 h)]

namespace DecoSet

end DecoSet

end MoveLemmas

section FormT

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

variable (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

def repD (c : (formGSD C Λ).Cl) : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) := (formGSD C Λ).outSec.rep c

def clsD (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : (formGSD C Λ).Cl := (formGSD C Λ).cls d

def dilD (P : ST) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (c : (formGSD C Λ).Cl) : (formGSD C Λ).Cl :=
  clsD C Λ ((repD C Λ c).dia1 P a)

end FormT

section Mem

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

@[reducible] def stepGSD (u : Pr.Word) (j : ℕ) : GSD X.K := formGSD (colVal W u j (Pr.vT u) Pr.vGs) (Λ j)

def stepEv (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) (j : ℕ) :
    (stepGSD W Λ u j).Ev σ₀ :=
  roundEv σ₀ hσ (W.lamTrue u j) (fun d => d.1.Lsh) (Λ j)

abbrev StCl (u : Pr.Word) (j : ℕ) : Type := (stepGSD W Λ u j).Cl

abbrev StStab (u : Pr.Word) (j : ℕ) (c : StCl W Λ u j) : Type :=
  MulAction.stabilizer (stepGSD W Λ u j).G ((stepGSD W Λ u j).outSec.rep c)

end Mem

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure DetChr (X : Fields) (m : ℕ) where
  mu : Fin m → Formalism.L2.DIV.Chr X.F X.E X.K
  chi : Formalism.L2.DIV.Chr X.F X.E X.K

namespace DetChr

variable {m : ℕ} (Dc : DetChr X m)

def muAt (i : ℕ) : Formalism.L2.DIV.Chr X.F X.E X.K := if h : i < m then Dc.mu ⟨i, h⟩ else 1

def Unit (σ₀ : X.K →+* ℂ) : Prop := (∀ j x, ‖σ₀ ((Dc.mu j x : X.Kˣ) : X.K)‖ = 1) ∧ ∀ x, ‖σ₀ ((Dc.chi x : X.Kˣ) : X.K)‖ = 1

end DetChr

variable (W : Wts X Pr.Word R) in
structure ChainGlob (σ₀ : X.K →+* ℂ) where
  hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)
  chr : DetChr X R.m
  chr_unit : chr.Unit σ₀

  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)

  S : Set ℕ

  ι : Type
  [ιFin : Fintype ι]

  mu : ι → Formalism.L2.DIV.Tup X.F X.E X.K S

  L : ∀ a, ChIdx X Pr R (QE sel (mu a : Formalism.L2.DIV.Chr X.F X.E X.K))
  twOk : ∀ a u j, (chF W sel (mu a) (L a) u j).Ok

attribute [instance] ChainGlob.ιFin

variable {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ}

end Glob

section Mem2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

set_option linter.unusedVariables false in
@[irreducible] def recDGamAll (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) : ℕ := dGamAut X R

variable {W Λ}

variable (W Λ) in
def repPt (hc : Formalism.BasicNotions.CMData X.F X.E) (u : Pr.Word) (j : ℕ) (c : StCl W Λ u j) : GL (Fin (R.N j)) (Formalism.L2.DIV.AfE X.F X.E) :=
  letI : NeZero (R.N j) := ⟨(R.N_pos j).ne'⟩
  ((ptOf hc (R.N j) (Pr.vT u) Pr.vGs ((stepGSD W Λ u j).outSec.rep c) : GL (Fin (R.N j)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))

open Classical in
def rhoK (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
    (Dc : DetChr X R.m) (u : Pr.Word) (i : ℕ) (c : StCl W Λ u i) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    (Formalism.L2.DIV.detTw hc.sig (Dc.muAt i) (repPt W Λ hc u i c))⁻¹ *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u i c)) ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ))
  else 1

open Classical in
def rhoK' (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
    (Dc : DetChr X R.m) (u : Pr.Word) (i : ℕ) (c : StCl W Λ u (i + 1)) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    Formalism.L2.DIV.detTw hc.sig (Dc.muAt i) (repPt W Λ hc u (i + 1) c) *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u (i + 1) c)) ^ (((R.N i / 2 : ℕ) : ℤ))
  else 1

variable (W) in
def sSharpC (u : Pr.Word) (i : ℕ) (τ : X.Tau) : ℤ := ⌊sExp' R ((RowPar.of (W.hc u τ)).eAt i) (i + 1)⌋

variable (W) in
def sDivC (u : Pr.Word) (i : ℕ) (τ : X.Tau) : ℤ := ⌊sExp R ((RowPar.of (W.hc u τ)).eAt i) (i + 1)⌋

def dePow (σ₀ : X.K →+* ℂ) (n : ℕ) (e : X.Tau → ℤ) (y : FrS X σ₀ n) : ℂ := ∏ τ, deFr y τ ^ e τ

variable (W Λ) in
structure ChainArg {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (u : Pr.Word) where
  kk : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1))
  unf : ∀ i, StCl W Λ u i → StCl W Λ u (i + 1) → ((FrS X σ₀ (R.N i) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N (i + 1)) → ℂ))
  unf_ev : ∀ i (L : StCl W Λ u i) (L' : StCl W Λ u (i + 1)) (x : (stepGSD W Λ u i).V),
    mulFun (fun y' => (dePow σ₀ (R.N (i + 1)) (sDivC W u i) y')⁻¹)
        (unf i L L' (mulFun (dePow σ₀ (R.N i) (sSharpC W u i)) ((stepEv W Λ σ₀ G.hσ u i).ev x))) =
      (σ₀ (rhoK W Λ G.chr u i L : X.K) * σ₀ (rhoK' W Λ G.chr u i L' : X.K))⁻¹ •
        (stepEv W Λ σ₀ G.hσ u (i + 1)).ev
          ((kk i).k ((stepGSD W Λ u i).outSec.rep L) ((stepGSD W Λ u (i + 1)).outSec.rep L') x)

def recUnf {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (u : Pr.Word) (kk : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1))) (i : ℕ)
    (L : StCl W Λ u i) (L' : StCl W Λ u (i + 1)) : (FrS X σ₀ (R.N i) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N (i + 1)) → ℂ) :=
  (σ₀ (rhoK W Λ G.chr u i L : X.K) * σ₀ (rhoK' W Λ G.chr u i L' : X.K))⁻¹ •
    ((mulFun (dePow σ₀ (R.N (i + 1)) (sDivC W u i))).comp
      (((stepEv W Λ σ₀ G.hσ u i).extend ((stepEv W Λ σ₀ G.hσ u (i + 1)).ev.comp
        ((kk i).k ((stepGSD W Λ u i).outSec.rep L) ((stepGSD W Λ u (i + 1)).outSec.rep L')))).comp
          (mulFun fun y => (dePow σ₀ (R.N i) (sSharpC W u i) y)⁻¹)))

def recChain (hX : X.Ok) (σ₀ : X.K →+* ℂ) (G : ChainGlob W σ₀) (u : Pr.Word) (A : ChainArg W Λ G u) :
    ColumnChain R X.Tau (W.hc u) where
  cls := StCl W Λ u
  clsFin := fun i => (stepOk W Λ hX u i).fintypeCl
  stab := StStab W Λ u
  stabGrp := fun _ _ => inferInstance
  stabFin := fun i c => (stepOk W Λ hX u i).fin_stab _
  DGam := recDGamAll W Λ hX G
  DGam_pos := recDGamAll_pos hX G
  dvd_DGam := fun j hj c => recDGamAll_dvd hX G u j hj c
  Y := fun i => FrS X σ₀ (R.N i)
  de := fun _ y τ => deFr y τ
  de_ne := fun _ y τ => (y.2 τ).ne_zero
  rhoDet := fun i c => σ₀ (rhoK W Λ G.chr u i c : X.K)
  rhoDet' := fun i c => σ₀ (rhoK' W Λ G.chr u i c : X.K)
  rho_norm := fun i _ c => rhoK_norm G u i c
  rho'_norm := fun i _ c => rhoK'_norm G u i c
  unf := A.unf
  sSharp := sSharpC W u
  sSharp_eq := fun i h τ => by
    obtain ⟨a, ha⟩ := (rec_sInt R (W.hc u τ) ⟨i, h⟩).2
    have e : (RowPar.of (W.hc u τ)).eAt i = (W.hc u τ).e ⟨i, h⟩ := by
      unfold RowPar.eAt
      rw [dite_eq_left h]
      rfl
    unfold sSharpC
    rw [e]
    simp only at ha
    rw [ha, Int.floor_intCast]
  sDiv := sDivC W u
  sDiv_eq := fun i h τ => by
    obtain ⟨a, ha⟩ := (rec_sInt R (W.hc u τ) ⟨i, h⟩).1
    have e : (RowPar.of (W.hc u τ)).eAt i = (W.hc u τ).e ⟨i, h⟩ := by
      unfold RowPar.eAt
      rw [dite_eq_left h]
      rfl
    unfold sDivC
    rw [e]
    simp only at ha
    rw [ha, Int.floor_intCast]

structure AtTNum where
  Dstar : ℝ
  Dstar_pos : 0 < Dstar
  GamP : ℝ
  one_lt_gammaP : 1 < GamP

variable (W Λ) in
def duStarC (u : Pr.Word) : ℕ :=
  Nat.card (formGSD (colVal W u 0 ∅ Pr.vGs) (Λ 0)).Cl * Module.finrank X.K (colVal W u 0 (∅ : Finset _) Pr.vGs).V

def rhoTC (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (hfree : (stepGSD W Λ u 0).Free) (P : {P // P ∈ Pr.vT u}) :
    (𝓞 X.E ⧸ P.1.asIdeal)ˣ →* ((StCl W Λ u 0 → FrS X σ₀ (R.N 0) → ℂ) →ₗ[ℂ] (StCl W Λ u 0 → FrS X σ₀ (R.N 0) → ℂ)) where
  toFun a := (stepEv W Λ σ₀ hσ u 0).opOn (DecoSet.dia1 P a)
  map_one' := by
    have : (DecoSet.dia1 P 1 : DecoSet (E := X.E) (n := R.N 0) (ST := Pr.vT u) (SG := Pr.vGs) → _) = fun d => d := funext fun d => diagonalTwist_one P d
    rw [this]
    exact (stepEv W Λ σ₀ hσ u 0).opOn_id hfree
  map_mul' a b := by
    have h := (stepEv W Λ σ₀ hσ u 0).opOn_comp hfree (DecoSet.dia1 P a) (DecoSet.dia1 P b) (fun _ _ => rfl)
    have e : (fun d : DecoSet (E := X.E) (n := R.N 0) (ST := Pr.vT u) (SG := Pr.vGs) => (d.dia1 P a).dia1 P b) = DecoSet.dia1 P (a * b) :=
      funext fun d => by rw [mul_comm, diagonalTwist_mul]
    rw [← e]
    exact h.symm

def recAtT (hX : X.Ok) (hPr : Pr.Ok) (hf : X.f = R.f) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (u : Pr.Word) (G : ChainGlob W σ₀) (A : ChainArg W Λ G u) (Ps : CharT X Pr) (hPs : Ps.Ok) (hfree : (stepGSD W Λ u 0).Free) (N : AtTNum) :
    ColumnsAtT R (recChain hX σ₀ G u A) where
  T := Pr.T u
  T_prime := hPr.T_prime u
  vT := {P // P ∈ Pr.vT u}
  vTFin := inferInstance
  card_vT := by rw [Fintype.card_coe, hPr.vT_card u, hf]
  Fv := fun P => 𝓞 X.E ⧸ P.1.asIdeal
  FvField := fun P => resField P.1
  FvFin := fun P => resFintype P.1
  FvDec := fun _ => Classical.decEq _
  card_Fv := fun P => by
    rw [← @Nat.card_eq_fintype_card _ (resFintype P.1)]
    exact card_quotient_eq_prime hPr u P
  psiT := fun P => Ps.psiC σ₀ u P
  psiT_ne := fun P => hPs.psiC_ne σ₀ u P
  rhoT := fun P => rhoTC σ₀ hσ u hfree P
  Mu0 := (stepEv W Λ σ₀ hσ u 0).Fi
  Mu0_fd := stepFi_fd hX σ₀ hσ u 0
  Mu0_stable := fun P a => by
    show Submodule.map ((stepEv W Λ σ₀ hσ u 0).opOn (DecoSet.dia1 P a)) (stepEv W Λ σ₀ hσ u 0).Fi ≤ _
    unfold GSD.Ev.Fi
    rw [Submodule.map_span_le]
    rintro _ ⟨φ, rfl⟩
    rw [step_opOn_dia]
    exact Submodule.subset_span ⟨_, rfl⟩
  duStar := duStarC W Λ u
  duStar_pos := duStarC_pos hX u
  Dstar := N.Dstar
  Dstar_pos := N.Dstar_pos
  GamP := N.GamP
  one_lt_gammaP := N.one_lt_gammaP

section Levs

variable {X : Fields} {Pr : Primes X} {R : Ranks}

end Levs

@[reducible] def stepH (hX : X.Ok) (u : Pr.Word) (j : ℕ) : HLat X.K :=
  (stepGSD W Λ u j).toH (stepOk W Λ hX u j) (stepGSD W Λ u j).intDel

variable (W Λ) in
def stepBv (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Submodule (𝓞 X.K) (stepGSD W Λ u j).EqFun :=
  (stepGSD W Λ u j).intOf fun d => BvLat W u j P d

structure XpArg {hc : X.Tau → HCParam R} (σ₀ : X.K →+* ℂ) (C : ColumnChain R X.Tau hc) (P : PeriodMap R C) where
  clsP : Type
  [clsPFin : Fintype clsP]
  stabilizer₂ : clsP → Type
  [stabPGrp : ∀ c, Group (stabilizer₂ c)]
  [stabPFin : ∀ c, Finite (stabilizer₂ c)]
  til : clsP → C.cls R.m
  stabMap : ∀ c, stabilizer₂ c →* C.stab R.m (til c)
  stabMap_inj : ∀ c, Function.Injective (stabMap c)
  evz_til : ∀ φ ψ : C.cls R.m → C.Y R.m → ℂ, (∀ c, φ (til c) = ψ (til c)) → P.evz φ = P.evz ψ
  ptC : Submodule ℂ P.Wrow
  ipP : P.Wrow →ₗ⋆[ℂ] P.Wrow →ₗ[ℂ] ℂ
  ptLat : HLat X.K
  ptLat_good : ptLat.Good
  ptEmb : ptLat.V →ₛₗ[σ₀] P.Wrow
  ptEmb_basis : LinearIndependent ℂ (fun a => ptEmb (ptLat.b a)) ∧
    Submodule.span ℂ (Set.range (fun a => ptEmb (ptLat.b a))) = ptC
  ptEmb_norm : ∀ x, (Formalism.HermitianLatticesTheory.majAt ptLat.b ptLat.X (InfinitePlace.mk σ₀) x x).re = (ipP (ptEmb x) (ptEmb x)).re
  beOn : X.Tau → ℝ
  beOn_nonneg : ∀ τ, 0 ≤ beOn τ
  thN : ∀ i, (X.K →+* ℂ) → C.cls i → C.cls (i + 1) → ℝ
  thN_nonneg : ∀ i s L L', 0 ≤ thN i s L L'
  thFree : ∀ i, (X.K →+* ℂ) → C.cls i → C.cls (i + 1) → ℝ
  thFree_nonneg : ∀ i s L L', 0 ≤ thFree i s L L'

open Classical in
def tauOfR (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : {P // P ∈ Pr.vT u} ≃ X.Tau :=
  haveI := hX.nonempty_Tau
  if hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal then Equiv.ofBijective _ (tauOfC_bijective hX hPr u w hw)
  else Fintype.equivOfCardEq (by rw [Fintype.card_coe, hPr.vT_card u]; rfl)

def recForms (hX : X.Ok) (hPr : Pr.Ok) (hf : X.f = R.f) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (u : Pr.Word) (G : ChainGlob W σ₀) (A : ChainArg W Λ G u) (Ps : CharT X Pr) (hPs : Ps.Ok) (hfree : (stepGSD W Λ u 0).Free) (N : AtTNum)
    (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K)) (P : PeriodMap R (recChain hX σ₀ G u A))
    (Xp : XpArg σ₀ (recChain hX σ₀ G u A) P) :
    MemberForms X.K σ₀ Pl X.Tau (W.hc u) (recChain hX σ₀ G u A) (recAtT hX hPr hf σ₀ hσ u G A Ps hPs hfree N) P where
  lv := fun i v c => (repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).lv v
  lvAcg := fun _ _ _ => inferInstance
  lvMod := fun i v c => (inferInstance : Module (𝓞 X.E ⧸ v.1.asIdeal) ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).lv v))
  lv_rank := fun i v c => DecoSet.lv_finrank (repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c) v
  fv := fun i v c => (repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).fv v
  fv_ne := fun i v c => (repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).fv_ne v
  up := fun i v c x => clsD _ (Λ i) ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).upL v (Pr.T u : 𝓞 X.E) x)
  upT := fun i v c x => (stepEv W Λ σ₀ hσ u i).trPt ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).upL v (Pr.T u : 𝓞 X.E) x)
  lk := fun i v c => (repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).lk v
  lkAcg := fun _ _ _ => inferInstance
  lkMod := fun i v c => (inferInstance : Module (𝓞 X.E ⧸ v.1.asIdeal) ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).lk v))
  lk_rank := fun i v c => DecoSet.lk_finrank (repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c) v
  te := fun i v c => (repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).te v (Pr.T u : 𝓞 X.E)
  te_ne := fun i v c => (repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).te_ne v (T_unif hX hPr u v).1 (T_unif hX hPr u v).2
  dn := fun i v c g => clsD _ (Λ i) ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).dnL v g)
  dnT := fun i v c g => (stepEv W Λ σ₀ hσ u i).trPt ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).dnL v g)
  dil := fun i v a c => dilD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) v a c
  dilT := fun i v a c => (stepEv W Λ σ₀ hσ u i).trPt ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).dia1 v a)
  dil_one := fun i v c => dilD_one _ _ v c
  dil_mul := fun i v a b c => dilD_mul _ _ v a b c
  dil_fv := fun i v a c => dilD_fv _ _ v a c
  dil_stab := fun i v a c => dilD_stab _ _ v a c
  rhoT_dil := fun _ _ _ _ => rfl
  tauOf := fun w => tauOfR hX hPr u (pw w)
  seenP := fun w => open Classical in decide (seenC Pr u (pw w))
  lam := fun j τ => W.lamN u j τ
  lam_eq := fun j hj τ i => Examples₂.lamOf_eq (W.hc u τ) j hj i
  sg := W.sgW
  Fi := fun i => (stepEv W Λ σ₀ hσ u i).Fi
  Fi_zero := rfl
  ipV := fun i _ => (stepEv W Λ σ₀ hσ u i).ip
  lat := fun i => stepH (W := W) (Λ := Λ) hX u i
  lat_good := fun i => stepH_good hX u i
  emb := fun i => (stepEv W Λ σ₀ hσ u i).emb
  emb_basis := fun i => ⟨(stepEv W Λ σ₀ hσ u i).emb_li (stepOk W Λ hX u i) _
    ((stepGSD W Λ u i).hB (stepOk W Λ hX u i)).linearIndependent, (stepEv W Λ σ₀ hσ u i).span_basis _⟩
  emb_norm := fun i x => (stepEv W Λ σ₀ hσ u i).norm_eq (stepOk W Λ hX u i) (stepRat W Λ hX u i) hσ x
  rhoT_lat := fun v a x hx => ⟨diamondOperatorOnForms' (colVal W u 0 (Pr.vT u) Pr.vGs) (Λ 0) v a x, step_dia_mem u 0 v a hx,
    (step_opOn_dia σ₀ hσ u 0 v a x).symm⟩
  Bw := fun i w v => Submodule.span (intW Pl w) (stepBv W Λ u i v : Set (stepGSD W Λ u i).EqFun)
  Bw_span := fun i w v => by
    rw [eq_top_iff, ← stepBv_span hX u i v]
    exact Submodule.span_mono Submodule.subset_span
  clsP := Xp.clsP
  clsPFin := Xp.clsPFin
  stabilizer₂ := Xp.stabilizer₂
  stabPGrp := Xp.stabPGrp
  stabPFin := Xp.stabPFin
  til := Xp.til
  stabMap := Xp.stabMap
  stabMap_inj := Xp.stabMap_inj
  evz_til := Xp.evz_til
  ptC := Xp.ptC
  ipP := Xp.ipP
  ptLat := Xp.ptLat
  ptLat_good := Xp.ptLat_good
  ptEmb := Xp.ptEmb
  ptEmb_basis := Xp.ptEmb_basis
  ptEmb_norm := Xp.ptEmb_norm
  beOn := Xp.beOn
  beOn_nonneg := Xp.beOn_nonneg
  thFree := Xp.thFree
  thFree_nonneg := Xp.thFree_nonneg

end Mem2

section Xp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

@[reducible] def rowGSD : GSD X.K := formGSD (rowVal W SG') ΛM

@[reducible] def ptGSD : GSD X.K :=
  formGSD (roundPk X W.sgTrue fun d : DecoSet (E := X.E) (n := R.N R.m - 1) (ST := ∅) (SG := SG') => d.1.N) ΛM.inv

def ptEv (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) : (ptGSD W ΛM).Ev σ₀ :=
  roundEv σ₀ hσ W.sgTrue (fun d => d.1.N) ΛM.inv

@[reducible] def ptH (hX : X.Ok) : HLat X.K := (ptGSD W ΛM).toH (ptOk W ΛM hX) (ptGSD W ΛM).intDel

variable {W ΛM}

def tilR (u : Pr.Word) (d : DecoSet (E := X.E) (n := R.N R.m - 1) (ST := ∅) (SG := SG')) : DecoSet (E := X.E) (n := R.N R.m) (ST := Pr.vT u) (SG := Pr.vGs) :=
  (DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).res hSG

variable (R) in
def extR : UF X.E (R.N R.m - 1) × GLG (E := X.E) (n := R.N R.m - 1) (SG := SG') →* UF X.E (R.N R.m) × GLG (E := X.E) (n := R.N R.m) (SG := Pr.vGs) :=
  MonoidHom.prodMap (extUH (N_m_succ R))
    ((MonoidHom.pi fun w : Pr.vGs => Pi.evalMonoidHom (fun w : SG' => GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal))
      ⟨w.1, hSG w.2⟩).comp (extGH (N_m_succ R)))

variable (ΛM) in
def LevExt : Prop := ∀ h : ↥(ΛM.inv).grp, (extR R hSG ((1 : UF X.E (R.N R.m - 1)), h.1)).2 ∈ (Λ R.m).grp

variable {Λ}

def extF (hL : LevExt Λ hSG ΛM) (u : Pr.Word) : (ptGSD W ΛM).G →* (stepGSD W Λ u R.m).G where
  toFun a := ((extR R hSG (a.1, a.2.1)).1, ⟨(extR R hSG (a.1, a.2.1)).2, hL a.2⟩)
  map_one' := by
    apply Prod.ext
    · exact map_one (extUH (N_m_succ R))
    · apply Subtype.ext
      exact congrArg Prod.snd (map_one (extR R hSG))
  map_mul' a b := by
    apply Prod.ext
    · exact map_mul (extUH (N_m_succ R)) a.1 b.1
    · apply Subtype.ext
      exact congrArg Prod.snd (map_mul (extR R hSG) (a.1, a.2.1) (b.1, b.2.1))

variable (W Λ ΛM) in
def tilCl (u : Pr.Word) (c : (ptGSD W ΛM).Cl) : StCl W Λ u R.m :=
  (stepGSD W Λ u R.m).cls (tilR hSG u ((ptGSD W ΛM).outSec.rep c))

def stabMapR (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExt Λ hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →* StStab W Λ u R.m (tilCl W Λ hSG ΛM u c) :=
  ((MulAut.conj ((stepGSD W Λ u R.m).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹).toMonoidHom.comp
    ((extF hSG hL u).comp (Subgroup.subtype _))).codRestrict _ (fun s => by
      rw [MulAction.mem_stabilizer_iff]
      show (((stepGSD W Λ u R.m).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹ * extF hSG hL u s.1 *
        ((stepGSD W Λ u R.m).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹⁻¹) •
          (stepGSD W Λ u R.m).outSec.rep (tilCl W Λ hSG ΛM u c) = _
      rw [inv_inv, mul_smul, mul_smul]
      have h1 : (stepGSD W Λ u R.m).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)) •
          (stepGSD W Λ u R.m).outSec.rep (tilCl W Λ hSG ΛM u c) = tilR hSG u ((ptGSD W ΛM).outSec.rep c) :=
        (stepGSD W Λ u R.m).outSec.mv_smul _
      rw [h1, ← tilR_smulF hSG hPr u hpi hL, s.2, inv_smul_eq_iff, h1])

def pairSemi (σ₀ : X.K →+* ℂ) {n : ℕ} (lam : X.Tau → DomWeight n) (y : VV X.K lam) : VV X.K lam →ₛₗ[σ₀] ℂ where
  toFun x := σ₀ (pairBK lam x y)
  map_add' x x' := by rw [map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  map_smul' a x := by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]

variable (W Λ ΛM) in
def lowC (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    (FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N R.m - 1) → ℂ) :=
  (stepEv W Λ σ₀ hσ u R.m).extend ((ptEv W ΛM σ₀ hσ).ev.comp (brC W u))

variable (W ΛM) in
def periodC (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (hM : (rowGSD W ΛM).Ok) :
    ((ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ) →ₗ[ℂ] (Fin ((rowGSD W ΛM).hDim hM) → ℂ) →ₗ[ℂ] ℂ :=
  (ptEv W ΛM σ₀ hσ).perCl (ptOk W ΛM hX) fun c a => pairSemi σ₀ W.sgTrue
    ((((rowGSD W ΛM).hB hM a : (rowGSD W ΛM).EqFun) : (rowGSD W ΛM).D → (rowGSD W ΛM).V) ((ptGSD W ΛM).outSec.rep c))

def recPer (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArg W Λ G u) (hM : (rowGSD W ΛM).Ok) : PeriodMap R (recChain hX σ₀ G u A) where
  Mt := Fin ((rowGSD W ΛM).hDim hM) → ℂ
  Wz := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m) → ℂ
  evz := (stepEv W Λ σ₀ hσ u R.m).evAt fun c => tilR hSG u ((ptGSD W ΛM).outSec.rep c)
  Wrow := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ
  lowerMap := LinearMap.pi fun c => lowC W Λ ΛM σ₀ hσ u ∘ₗ LinearMap.proj c
  period := periodC W ΛM hX σ₀ hσ hM

structure ThArg (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (u : Pr.Word) where

  beOn : X.Tau → ℝ
  beOn_nonneg : ∀ τ, 0 ≤ beOn τ

  thN : ∀ i, (X.K →+* ℂ) → StCl W Λ u i → StCl W Λ u (i + 1) → ℝ
  thN_nonneg : ∀ i s L L', 0 ≤ thN i s L L'

  thFree : ∀ i, (X.K →+* ℂ) → StCl W Λ u i → StCl W Λ u (i + 1) → ℝ
  thFree_nonneg : ∀ i s L L', 0 ≤ thFree i s L L'

def recXp (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArg W Λ G u) (hM : (rowGSD W ΛM).Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExt Λ hSG ΛM)
    (Th : ThArg W Λ u) : XpArg σ₀ (recChain hX σ₀ G u A) (recPer hSG hX σ₀ hσ u G A hM) where
  clsP := (ptGSD W ΛM).Cl
  clsPFin := (ptOk W ΛM hX).fintypeCl
  stabilizer₂ := fun c => MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c)
  stabPGrp := fun _ => inferInstance
  stabPFin := fun _ => (ptOk W ΛM hX).fin_stab _
  til := tilCl W Λ hSG ΛM u
  stabMap := stabMapR hSG hPr u hpi hL
  stabMap_inj := stabMapR_injective hSG hPr u hpi hL
  evz_til := fun φ ψ h => by
    funext c
    show (stepEv W Λ σ₀ hσ u R.m).trPt _ (φ (tilCl W Λ hSG ΛM u c)) = (stepEv W Λ σ₀ hσ u R.m).trPt _ (ψ (tilCl W Λ hSG ΛM u c))
    rw [h c]
  ptC := (ptEv W ΛM σ₀ hσ).Fi
  ipP := (ptEv W ΛM σ₀ hσ).ipCl (ptOk W ΛM hX)
  ptLat := ptH W ΛM hX
  ptLat_good := ptH_good W ΛM hX
  ptEmb := (ptEv W ΛM σ₀ hσ).emb
  ptEmb_basis := ⟨(ptEv W ΛM σ₀ hσ).emb_li (ptOk W ΛM hX) _ ((ptGSD W ΛM).hB (ptOk W ΛM hX)).linearIndependent,
    (ptEv W ΛM σ₀ hσ).span_basis _⟩
  ptEmb_norm := fun x => (ptEv W ΛM σ₀ hσ).norm_ipCl (ptOk W ΛM hX) (ptRat W ΛM hX) hσ x
  beOn := Th.beOn
  beOn_nonneg := Th.beOn_nonneg
  thN := Th.thN
  thN_nonneg := Th.thN_nonneg
  thFree := Th.thFree
  thFree_nonneg := Th.thFree_nonneg

end Xp

section Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}

end Ker

section Fam

variable {K : Type} [Field K] [NumberField K] [StarRing K]

@[reducible] def cplGSD {S : GSD K} (Y : Cpl S) : GSD K where
  G := S.G
  D := Y.Pts
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab p := S.Nab p.1.1
  Del p := S.Del p.1.1

variable {X : Fields} {R : Ranks}

end Fam

section NonDeg

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}

end NonDeg

section Ram

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}

end Ram

section All

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') {ΛM : LevFam X.E X.K (R.N R.m - 1) SG'}

def recFormsX (hX : X.Ok) (hPr : Pr.Ok) (hf : X.f = R.f) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (u : Pr.Word) (G : ChainGlob W σ₀) (A : ChainArg W Λ G u) (Ps : CharT X Pr) (hPs : Ps.Ok) (hfree : (stepGSD W Λ u 0).Free) (N : AtTNum)
    (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K)) (hM : (rowGSD W ΛM).Ok)
    (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExt Λ hSG ΛM) (Th : ThArg W Λ u) :
    MemberForms X.K σ₀ Pl X.Tau (W.hc u) (recChain hX σ₀ G u A) (recAtT hX hPr hf σ₀ hσ u G A Ps hPs hfree N)
      (recPer hSG hX σ₀ hσ u G A hM) :=
  recForms hX hPr hf σ₀ hσ u G A Ps hPs hfree N Pl pw (recPer hSG hX σ₀ hσ u G A hM) (recXp hSG hX hPr σ₀ hσ u G A hM hpi hL Th)

end All

section Mink

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}

variable {σ₀ : X.K →+* ℂ}

end Mink

section FrmMink

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoF X.E n ST SG Q)) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)

end FrmMink

section TwMinkS

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ}

end TwMinkS

end Formalism.L2.Col
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.Columns.Record =====
