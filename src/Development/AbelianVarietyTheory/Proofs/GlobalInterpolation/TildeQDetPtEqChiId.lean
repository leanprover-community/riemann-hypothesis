module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MkDetPtEqRelDetQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubStdL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactor
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
import Mathlib.Tactic.Linter.HaveILetI
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

theorem tildeQ_detPt_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : GlobalTheory.Mem.Chr.HFrame H e) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))), letI := H.cmStar; ∀ (p : DecoF H.E n ST SG Q), LevOk H SG SQ → ((tildeQ H SQ C.chiPsi (detPt H SQ p) : ℂˣ) : ℂ) = chiId C.chiPsi (Th.detId H (Th.stdL H n) p.deco.1.N) := by
  intro R H e C n ST SG Q SQ
  letI := H.cmStar
  intro p hL
  have hχ := C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor R H).2.2.2 C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  rw [tildeQ_eq_comp H SQ hK, MonoidHom.comp_apply]
  exact tildeD_eq_chiId R H C.chiPsi hχ n _ p.deco.2.lat _
    (congrArg (toDtTMod H SQ) (mk_detPt_eq_relDetQ R H n ST SG Q SQ p hL))

end GlobalTheory.Mem.ChiDet
