module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelHalfChainNumbersAnyLevelPrime
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.kernelHalf_chainNumbers_any_levelPrime : ∀ CY : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) [_root_.NumberField.IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu = 1 → cst.sharp = true → I.Ok Ch sel mu cst G (N.R.m - 2) → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Reads N eJ δ (Pr.T u) R → KerSide R (InfinitePlace X.K) C (FactorBounds (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) fun l => (eJ l).1) := by
  first | exact @GlobalTheory.KernelHalfS.kerSide_chainS | exact GlobalTheory.KernelHalfS.kerSide_chainS | (intros; apply GlobalTheory.KernelHalfS.kerSide_chainS <;> assumption)
