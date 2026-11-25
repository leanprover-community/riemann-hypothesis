module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniqueIsContr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.Rigid

theorem isSpherical_locProd {E : Type} [Field E] [NumberField E] {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (w : HeightOneSpectrum (𝓞 E)) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (hs : ∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (GlobalTheory.LFun.KGL w (n := (N i)))) :
    GlobalTheory.LGrp.IsSpherical (GlobalTheory.UnitaryBC.locProd h w σ) (GlobalTheory.LFun.KGL w (n := n)) := by
  have hKO : ∀ m, GlobalTheory.LFun.KGL w (n := m) = KO (w.adicCompletion E) (Fin m) := fun m =>
    (GlobalTheory.SmGL.SphCompletion.KO_completion w m).symm
  choose v hv hv0 using fun i => (Submodule.ne_bot_iff _).1 (hs i)
  obtain ⟨f, hf, hf1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (k := w.adicCompletion E) (stdBlocks N h)
    (ρ := piTensor fun i => (σ i).ρ) (x := PiTensorProduct.tprod ℂ v) (fun g hg => by
      rw [piTensor_tprod]
      congr 1
      funext i
      exact GlobalTheory.LGrp.mem_fixed.1 (hv i) (g i) (by rw [hKO]; exact hg i))
  refine (Submodule.ne_bot_iff _).2 ⟨f, by rw [hKO]; exact hf, fun h0 => GlobalTheory.ContrObj.tprod_ne_zero v hv0 ?_⟩
  rw [← hf1, h0]
  rfl

end GlobalTheory.Rigid
