module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongW Formalism.UG GlobalTheory.DefU GlobalTheory.PRep GlobalTheory.CongSc

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

variable [IsCMField E]

theorem cT_cLoc_conjSrc_mul {n : ℕ} (g : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    Matrix.transpose (((cLoc (conjSrc (IsCMField.complexConj E).toRingEquiv u) g : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _).map (conjLoc (IsCMField.complexConj E).toRingEquiv u)) *
      ((cLoc u g : GL (Fin n) (u.adicCompletion E)) : Matrix (Fin n) (Fin n) (u.adicCompletion E)) = 1 := by
  have h : cT (conjAd E) ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) * 1 *
      ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) = 1 := g.2
  rw [Matrix.mul_one] at h
  calc _ = (cT (conjAd E) ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) *
        ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E))).map ((pLoc E u).comp (pFin E)) := by
        rw [Matrix.map_mul]; rfl
    _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

end GlobalTheory.LadicPair
