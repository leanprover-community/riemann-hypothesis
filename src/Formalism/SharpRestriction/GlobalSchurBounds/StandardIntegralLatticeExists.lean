import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.FormalGroupJets
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.GlobalSchurBounds.KernelEntryData
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.LocalRingCardinality.SpanPowerMembership

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Inhab

open Formalism.BasicNotions NumberField







def ChiEx (D : D7) : Prop := ∃ χ, Formalism.MainNotions.TaylorLogMetric.IsChi D χ




section PosSec

open Formalism.FrobeniusOrbits

def prPsi (e : Formalism.HC.Frame) : e.GG →* e.GG where
  toFun g := ((g.1.1 * g.1.2, 1), g.2)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp [mul_mul_mul_comm]
    · simp
    · simp






def IsFrobOf (D : D7) (p : ℕ) (φ : D.R.GG) : Prop :=
  ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
    IsArithFrobAt ℤ (D.host.sigmaOf φ) P




end PosSec

section Std

variable (D : D7)

theorem mem_stdL {N : ℕ} (x : Fin N → D.host.E) :
    x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N ↔ ∀ i, x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  unfold Formalism.MainNotions.StandardLatticesGL3.stdL
  simp [Submodule.mem_pi, Submodule.mem_one]

theorem single_mem_stdL {N : ℕ} (a : Fin N) : (Pi.single a 1 : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
  rw [mem_stdL]
  intro i
  by_cases h : i = a
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem star_mem_range (x : D.host.E) (h : x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    (letI := D.host.cmStar; star x) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  let _ := D.host.cmStar
  have h1 : IsIntegral ℤ x := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).2 h
  have h2 : IsIntegral ℤ (starRingEnd D.host.E x) := map_isIntegral_int (starRingEnd D.host.E) h1
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 h2

theorem stdL_isSD (N : ℕ) : (letI := D.host.cmStar; IsSDLat D.host.E N (Formalism.MainNotions.StandardLatticesGL3.stdL D N)) := by
  let _ := D.host.cmStar
  refine ⟨?_, ?_, ?_⟩
  · have : Formalism.MainNotions.StandardLatticesGL3.stdL D N =
        Submodule.span (𝓞 D.host.E) (Set.range fun a : Fin N => (Pi.single a 1 : Fin N → D.host.E)) := by
      apply le_antisymm
      · intro x hx
        rw [mem_stdL] at hx
        choose c hc using hx
        have : x = ∑ a, c a • (Pi.single a 1 : Fin N → D.host.E) := by
          funext i
          simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
        rw [this]
        exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        exact single_mem_stdL D a
    rw [this]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [Submodule.eq_top_iff']
    intro x
    have : x = ∑ a, x a • (Pi.single a 1 : Fin N → D.host.E) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdL D a))
  · intro y
    constructor
    · intro hy x hx
      rw [mem_stdL] at hx hy
      unfold stdH
      exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (star_mem_range D _ (hx i)) (hy i)
    · intro h
      rw [mem_stdL]
      intro i
      have := h _ (single_mem_stdL D i)
      unfold stdH at this
      simpa [Pi.single_apply, apply_ite star] using this


theorem Adm_std (N N' : ℕ) (h : Even N) (h' : Even N') :
    Formalism.MainNotions.TaylorLogMetric.admitted D N N' (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') :=
  ⟨h, h', stdL_isSD D N, stdL_isSD D N'⟩




theorem lamC_one {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) : Formalism.MainNotions.TaylorLogMetric.lamC lam 1 = 1 := by
  unfold Formalism.MainNotions.TaylorLogMetric.lamC
  rw [dif_pos (one_mem _)]
  exact map_one lam



end Std

section KernelEntryData

variable (p : ℕ) [Fact p.Prime]


theorem norm_p_Cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]



end KernelEntryData

section ReadsSec

open Formalism.MainNotions.Lnk Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain


end ReadsSec

section FrobSec

open Formalism.FrobeniusOrbits
open scoped Pointwise





end FrobSec

section Junk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes




def GaugeEx (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  ∃ G : GaugeFam F E σ, G.IsGauge

end Junk

end Formalism.MainNotions.GlobalTheoryTheory.Inhab

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Inhab

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar





def TorusEx (D : D7) : Prop := ∀ (i : ℕ) (s : D.what₂.LL →+* ℂ), Nonempty (Torus D i s)

def ThetaEx (D : D7) : Prop :=
  ∀ (i : ℕ) (s : D.what₂.LL →+* ℂ), ∃ (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ) (cf : (Gx D i →₀ ℕ) → ℂ),
    T.Admis Th ∧ T.l2Sq Th = 1 ∧ ∀ z, HasSum (fun e => cf e * e.prod fun g n => z g ^ n) (Th z)








theorem Hq_sub (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (z x : Gx D i → ℂ) :
    Hq D i s (z - x) = Hq D i s z - 2 * (Hherm D i s z x).re + Hq D i s x := by
  unfold Hq Hherm
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Complex.div_ofReal_re, Pi.sub_apply, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_sub, Complex.star_def]
  ring

theorem dens_trans (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (x : Gx D i → ℂ) (Th : (Gx D i → ℂ) → ℂ)
    (z : Gx D i → ℂ) : dens D i s (trans D i s x Th) z = dens D i s Th (z - x) := by
  unfold dens flipTwoThree.trans
  rw [norm_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, Hq_sub]
  congr 2
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  push_cast
  ring


theorem trans_zero (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th : (Gx D i → ℂ) → ℂ) :
    trans D i s 0 Th = Th := by
  funext z
  simp [flipTwoThree.trans, Hherm, Hq]




end Formalism.MainNotions.GlobalTheoryTheory.Inhab

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Inhab

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

attribute [local instance] Formalism.BasicNotions.Host.cmStar




theorem exists_ext (D : D7) (ρ : D.host.E →+* D.what₂.LL) (σ : D.host.E →+* ℂ) :
    ∃ s : D.what₂.LL →+* ℂ, ∀ a, s (ρ a) = σ a := by
  let _ := ρ.toAlgebra
  let _ := σ.toAlgebra
  have : Algebra.IsAlgebraic D.host.E D.what₂.LL := by
    have : IsScalarTower ℚ D.host.E D.what₂.LL := IsScalarTower.of_algebraMap_eq (fun q => by
      simp [RingHom.algebraMap_toAlgebra])
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) D.host.E
  let f : D.what₂.LL →ₐ[D.host.E] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun a => f.commutes a⟩



structure ColBase (D : D7) (u : D.what₂.Word) where
  rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)
  Q : (D.mem u).C.cls 0 → D.what₂.Tau → HLat D.what₂.LL
  Q_good : ∀ c τ, (Q c τ).Good
  eQ : ∀ c τ, (Q c τ).ι ≃ Fin (D.R.N 0)
  bc : ∀ c τ, (D.sp.X 0).V →+ (Q c τ).V
  bc_smul : ∀ c τ (a : D.host.E) y, bc c τ (a • y) = rho τ a • bc c τ y
  bc_L : ∀ c τ, (Q c τ).L = Submodule.span (𝓞 D.what₂.LL) (bc c τ '' (D.clsLat u 0 c : Set (D.sp.X 0).V))
  bc_norm : ∀ c τ (v : InfinitePlace D.what₂.LL) y,
    (Formalism.HermitianLatticesTheory.majAt (Q c τ).b (Q c τ).X v (bc c τ y) (bc c τ y)).re =
      (v.embedding (rho τ ((D.sp.X 0).hT y y))).re

def ColTie {D : D7} {u : D.what₂.Word} (B : ColBase D u) : Prop :=
  Nonempty ((D.mem u).C.cls 0) ∧
  (∀ c, LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c)) ∧
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ (w : D.what₂.places.Pl)
      (γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL),
      (∀ c τ, LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) →
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (nfAll ((D.fm u).lam 0)
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem ColVal_nonempty_iff (D : D7) (u : D.what₂.Word) :
    Nonempty (ColVal D u) ↔ ∃ B : ColBase D u, ColTie B := by
  constructor
  · rintro ⟨CV⟩
    exact ⟨⟨CV.rho, CV.Q, CV.Q_good, CV.eQ, CV.bc, CV.bc_smul, CV.bc_L, CV.bc_norm⟩,
      CV.ne, CV.latT, CV.co, CV.co_inj, CV.co_range, CV.fin, CV.inf⟩
  · rintro ⟨B, hne, hT, co, h1, h2, h3, h4⟩
    exact ⟨⟨hne, B.rho, B.Q, B.Q_good, B.eQ, B.bc, B.bc_smul, B.bc_L, B.bc_norm, hT, co, h1, h2, h3, h4⟩⟩

def PosFrame (D : D7) : Prop :=
  ∀ σ : D.host.E →+* ℂ, ∃ Y : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) ℂ, IsUnit Y.det ∧
    ∀ y : (D.sp.X 0).V, ∑ i, ‖(Y.mulVec fun j => σ ((D.sp.X 0).frame.repr y j)) i‖ ^ 2 =
      (σ ((D.sp.X 0).hT y y)).re

section Base

variable {E LL : Type} [Field E] [NumberField E] [StarRing E] [Field LL] [NumberField LL] [StarRing LL]
  (S : HSpace E) (ρ : E →+* LL)

def bcFun : S.V →+ (Fin S.rank → LL) where
  toFun y i := ρ (S.frame.repr y i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem bcFun_smul (a : E) (y : S.V) : bcFun S ρ (a • y) = ρ a • bcFun S ρ y := by
  funext i; simp [bcFun]

theorem bcFun_smulO (a : 𝓞 E) (y : S.V) :
    bcFun S ρ (a • y) = (RingOfIntegers.mapRingHom ρ a) • bcFun S ρ y := by
  have h1 : a • y = (a : E) • y := (algebraMap_smul E a y).symm
  rw [h1, bcFun_smul]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  congr 1

theorem bcFun_frame (i : Fin S.rank) : bcFun S ρ (S.frame i) = Pi.single i 1 := by
  funext j
  simp only [bcFun, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Module.Basis.repr_self]
  by_cases h : j = i
  · subst h; simp
  · rw [Finsupp.single_eq_of_ne (by simpa using h), Pi.single_eq_of_ne h, map_zero]

def mkQ (Lc : Submodule (𝓞 E) S.V) (Y : InfinitePlace LL → Matrix (Fin S.rank) (Fin S.rank) ℂ) : HLat LL where
  V := Fin S.rank → LL
  ι := Fin S.rank
  b := Pi.basisFun LL (Fin S.rank)
  X := fun v => (Y v)⁻¹
  L := Submodule.span (𝓞 LL) (bcFun S ρ '' (Lc : Set S.V))

theorem mkQ_fg (Lc : Submodule (𝓞 E) S.V) (h : Lc.FG) :
    (Submodule.span (𝓞 LL) (bcFun S ρ '' (Lc : Set S.V))).FG := by
  classical
  obtain ⟨s, hs⟩ := h
  refine ⟨s.image (bcFun S ρ), ?_⟩
  apply le_antisymm
  · apply Submodule.span_mono
    rw [Finset.coe_image]
    apply Set.image_mono
    rw [← hs]; exact Submodule.subset_span
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [← hs] at hy
    rw [Finset.coe_image]
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [bcFun_smulO]; exact Submodule.smul_mem _ _ hx

theorem mkQ_span (Lc : Submodule (𝓞 E) S.V) (h : Submodule.span E (Lc : Set S.V) = ⊤) :
    Submodule.span LL ((Submodule.span (𝓞 LL) (bcFun S ρ '' (Lc : Set S.V)) : Submodule (𝓞 LL) (Fin S.rank → LL)) :
      Set (Fin S.rank → LL)) = ⊤ := by
  have key : ∀ y : S.V, bcFun S ρ y ∈ Submodule.span LL (bcFun S ρ '' (Lc : Set S.V)) := by
    intro y
    have hy : y ∈ Submodule.span E (Lc : Set S.V) := by rw [h]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [bcFun_smul]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i, w i • (Pi.single i 1 : Fin S.rank → LL) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  rw [← bcFun_frame S ρ i]
  exact Submodule.span_mono Submodule.subset_span (key _)

theorem mkQ_norm (Lc : Submodule (𝓞 E) S.V) (Y : InfinitePlace LL → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (hY : ∀ v, IsUnit (Y v).det) (v : InfinitePlace LL) (y : S.V) :
    (Formalism.HermitianLatticesTheory.majAt (mkQ S ρ Lc Y).b (mkQ S ρ Lc Y).X v (bcFun S ρ y) (bcFun S ρ y)).re =
      ∑ i, ‖((Y v).mulVec fun j => (v.embedding.comp ρ) (S.frame.repr y j)) i‖ ^ 2 := by
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : Formalism.HermitianLatticesTheory.fcoord (mkQ S ρ Lc Y).b (mkQ S ρ Lc Y).X v (bcFun S ρ y) =
      (Y v).mulVec fun j => (v.embedding.comp ρ) (S.frame.repr y j) := by
    unfold Formalism.HermitianLatticesTheory.fcoord
    have : ((mkQ S ρ Lc Y).X v)⁻¹ = Y v := Matrix.nonsing_inv_nonsing_inv _ (hY v)
    rw [this]
    congr 1
  rw [h1]
  simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]

theorem base_exists (Lc : Submodule (𝓞 E) S.V) (hfg : Lc.FG) (hsp : Submodule.span E (Lc : Set S.V) = ⊤)
    (n : ℕ) (hr : S.rank = n)
    (hpos : ∀ σ : E →+* ℂ, ∃ Y : Matrix (Fin S.rank) (Fin S.rank) ℂ, IsUnit Y.det ∧
      ∀ y : S.V, ∑ i, ‖(Y.mulVec fun j => σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re) :
    ∃ (Q : HLat LL) (_ : Q.ι ≃ Fin n) (bc : S.V →+ Q.V), Q.Good ∧ (∀ (a : E) y, bc (a • y) = ρ a • bc y) ∧
      Q.L = Submodule.span (𝓞 LL) (bc '' (Lc : Set S.V)) ∧
      ∀ (v : InfinitePlace LL) y, (Formalism.HermitianLatticesTheory.majAt Q.b Q.X v (bc y) (bc y)).re = (v.embedding (ρ (S.hT y y))).re := by
  choose Y hY hN using hpos
  refine ⟨mkQ S ρ Lc (fun v => Y (v.embedding.comp ρ)), finCongr hr, bcFun S ρ,
    ⟨fun v => Matrix.isUnit_nonsing_inv_det _ (hY _), mkQ_fg S ρ Lc hfg, mkQ_span S ρ Lc hsp⟩,
    bcFun_smul S ρ, rfl, fun v y => ?_⟩
  exact (mkQ_norm S ρ Lc (fun v => Y (v.embedding.comp ρ)) (fun v => hY _) v y).trans (hN _ y)

end Base

theorem ColBase_exists (D : D7) (u : D.what₂.Word) (h : PosFrame D)
    (rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) : ∃ B : ColBase D u, B.rho = rho := by
  have key := fun (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) =>
    base_exists (LL := D.what₂.LL) (D.sp.X 0) (rho τ) (D.clsLat u 0 c) (D.clsLat_lat u 0 c).fg
      (D.clsLat_lat u 0 c).span_eq_top (D.R.N 0) (D.sp.X_rank 0 (Nat.zero_le _)) h
  choose Q eQ bc h1 h2 h3 h4 using key
  exact ⟨⟨rho, Q, h1, eQ, bc, h2, h3, h4⟩, rfl⟩



theorem host_emb_star (D : D7) (σ : D.host.E →+* ℂ) (a : D.host.E) : σ (star a) = (starRingEnd ℂ) (σ a) := by
  have := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E σ a






section LocB

variable {LL : Type} [Field LL] (Pl : Rows.Places LL) (w : Pl.Pl) {V : Type} [AddCommGroup V] [Module LL V]


end LocB

def IntInW (D : D7) (w : D.what₂.places.Pl) : Prop := ∀ z : 𝓞 D.what₂.LL, (z : D.what₂.LL) ∈ intW D.what₂.places w





end Formalism.MainNotions.GlobalTheoryTheory.Inhab

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Inhab

open Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar






def BeOnIsNorm (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
    ∀ τ, (D.fm u).beOn τ = product_first_zeroth_parts.opNorm D u τ (br τ)


theorem opNorm_zero (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : product_first_zeroth_parts.opNorm D u τ 0 = 0 := by
  unfold product_first_zeroth_parts.opNorm
  apply le_antisymm
  · apply Real.sSup_le _ le_rfl
    rintro x ⟨f, -, rfl⟩
    simp [normFock, Formalism.REAL.fockF]
  · apply Real.sSup_nonneg
    rintro x ⟨f, -, rfl⟩
    exact Real.sqrt_nonneg _

def pendJunk (D : D7) (u : D.what₂.Word) (hE : IsEmpty (D.fm u).clsP) (hC : (D.fm u).ptC = ⊥)
    (hI : (D.fm u).SgInterlace)
    (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
      MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
    (hb : ∀ τ, (D.fm u).beOn τ = product_first_zeroth_parts.opNorm D u τ (br τ)) : product_first_zeroth_parts.Pend D u where
  br := br
  coM := fun _ _ => 0
  coP := fun _ => 0
  coM_mem := fun _ c => hE.elim c
  coM_inj := fun _ c => hE.elim c
  coP_mem := fun _ _ _ c => hE.elim c
  coP_inj := fun _ z hz _ => by rw [hC] at hz; exact (Submodule.mem_bot ℂ).1 hz
  Pt_eq := fun _ _ _ c => hE.elim c
  lat_co := fun _ _ _ c => hE.elim c
  pt_co := fun w z hz => by
    rw [hC] at hz
    have hz0 : z = 0 := (Submodule.mem_bot ℂ).1 hz
    exact ⟨fun _ c => hE.elim c, fun _ => ⟨0, Submodule.zero_mem _, by rw [hz0, map_zero]⟩⟩
  gP := fun _ _ _ => 1
  ipV_co := fun _ c => hE.elim c
  re_petersson_self_eq_sum_coord := fun w z hz => by
    rw [hC] at hz
    have hz0 : z = 0 := (Submodule.mem_bot ℂ).1 hz
    subst hz0
    simp
  beOn_eq := hb
  interlace := hI





theorem emb_mem_Fi (D : D7) (u : D.what₂.Word) (i : ℕ) (x : ((D.fm u).lat i).V) :
    (D.fm u).emb i x ∈ (D.fm u).Fi i := by
  rw [← ((D.fm u).emb_basis i).2, ← ((D.fm u).lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem blk_IntSpan (D : D7) {n n' : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n)
    (sg : D.what₂.Tau → DomWeight n')
    (br : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ)
    (h : ∀ τ, ∀ f ∈ delSq ℤ n (lam τ), ∃ g ∈ delSq ℤ n' (sg τ),
      br τ (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g)
    (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hp : p ∈ product_first_zeroth_parts.IntSpan D w lam) :
    product_first_zeroth_parts.blk (fun τ => br τ) p ∈ product_first_zeroth_parts.IntSpan D w sg := by
  unfold product_first_zeroth_parts.IntSpan at hp
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hp
    choose g hg hbg using fun τ => h τ (f τ) (hf τ)
    rw [map_smul, product_first_zeroth_parts.blk_ten]
    exact AddSubgroup.subset_closure ⟨r, g, hr, hg, by simp only [hbg]⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [map_neg]; exact AddSubgroup.neg_mem _ ha




end Formalism.MainNotions.GlobalTheoryTheory.Inhab
