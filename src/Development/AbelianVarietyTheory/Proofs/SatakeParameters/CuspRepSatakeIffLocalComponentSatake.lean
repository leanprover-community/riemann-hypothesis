module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem GlobalTheory.Cong.satake_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ → (∀ B, (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ ↔ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥) := by
  intro E _ _ _ a π w σ hσ
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  refine ⟨fun B => ⟨fun hB => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ h⟩, ?_⟩
  · have hB' : GlobalTheory.LFun.HasSatGL w (π.locRep w) B := hB
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
    obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
      (fun f : LocSph.Maps π w σ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL w (n := a) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
      (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
      (by rw [LocSph.iSup_range_eq π w σ hσ]; exact x.2)
    obtain ⟨B', hB''⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
      ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
    exact (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hB'').unique hB' ▸ hB''
  · unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
    rw [hK]

end
