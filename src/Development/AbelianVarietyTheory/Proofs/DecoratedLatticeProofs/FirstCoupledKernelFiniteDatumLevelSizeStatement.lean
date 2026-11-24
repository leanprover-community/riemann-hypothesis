module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstCoupledKernelFiniteDatumLevelSize
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  first | exact @GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp | exact GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp | (intros; apply GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp <;> assumption)
