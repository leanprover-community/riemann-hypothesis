module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGalois
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.FrobTwistKappa

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  intro l _ K bk τ d ρ s g G Φ i Ψ V ε hG hΦ hi hΨ hκ h
  have hsmul : ∀ (f : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (c • M).map f = f c • M.map f := fun f c M => by ext a b; simp
  have hΦG : ∀ x, Φ (G x) = G (Φ x) := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l)) =
        (Per.σA (g : GQ l)).comp WittVector.frobenius :=
      RingHom.ext fun a => (GlobalTheory.Prism.PullGal.σA_frobenius (g : GQ l) a).symm
    have hc := (GlobalTheory.BSP.FrobRational.isDiscMap_comp hG hΦ).unique
      (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΦ hG)
    exact fun x => RingHom.congr_fun hc x
  have hΦi : Φ.comp i = i.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (GlobalTheory.BSP.FrobRational.isDiscMap_comp hi hΦ).unique (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΨ hi)
  have hΦiS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (toDisc l (bk.ev X) bk.ρ₀ (bk.ev x)) = toDisc l (bk.ev X) bk.ρ₀ (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have hFD : (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C)).map i = s.F.map (bk.iS.comp C) := by
    ext a b
    exact hi.ext _
  have hGFD : (s.F.map (bk.iS.comp C)).map G = s.F.map (bk.iS.comp C) := by
    ext a b
    change G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev (C (s.F a b)))) = toDisc l (bk.ev X) bk.ρ₀ (bk.ev (C (s.F a b)))
    rw [hG.ext, bk.ev_C, bk.gal_w]
  have e1 : (V.map i).map Φ = (V.map Ψ).map i := by
    ext a b
    exact RingHom.congr_fun hΦi (V a b)
  have e2 : (ε.map bk.iA).map Φ = (ε.map WittVector.frobenius).map bk.iA := by
    ext a b
    exact hΦ.ext _
  have e3 : ((V.map i).map G).map Φ = ((V.map Ψ).map i).map G := by
    ext a b
    simp only [Matrix.map_apply]
    rw [hΦG]
    exact congrArg G (RingHom.congr_fun hΦi (V a b))
  have h1 := congrArg (fun M => M.map Φ) h
  simp only [hsmul, Matrix.map_mul] at h1
  rw [map_pow, map_pow, hΦG, hΦiS, e1, e2, e3] at h1
  have eL : (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i =
      s.F.map (bk.iS.comp C) * (V.map Ψ).map i := by
    rw [Matrix.map_mul, hFD]
  rw [eL, Matrix.map_mul, hGFD, Matrix.mul_assoc (s.F.map (bk.iS.comp C)), ← Matrix.mul_assoc (s.κ g), hκ,
    Matrix.mul_assoc]
  have h2 := congrArg (fun M => s.F.map (bk.iS.comp C) * M) h1
  simp only [Matrix.mul_smul] at h2
  exact h2

end GlobalTheory.BKLim.FrobTwistKappa
