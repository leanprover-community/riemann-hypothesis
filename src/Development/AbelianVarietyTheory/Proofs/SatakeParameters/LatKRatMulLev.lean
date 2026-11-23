module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdXMulLev
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem latK_rat_mul_lev : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (a : 𝓞 D.host.E) (x : GL (Fin N) (AfE D.host.F D.host.E)) (κ : S.U), ∀ g ∈ UJ (sigD D : D.host.E →+* D.host.E) J, latK D.sp J a (GlobalTheory.TwU.ratA D.host.F g * x * κ.1) S.Lb = SDLat.smulLat (eMat rfl (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (latK D.sp J a x S.Lb) := by
  intro D N J T f bad S a x κ g hg
  letI := D.host.cmStar
  rw [Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ g hg (GlobalTheory.TwU.hatStab_of_lev S κ)]
  unfold SDLat.smulLat eMat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV.Xc

end
