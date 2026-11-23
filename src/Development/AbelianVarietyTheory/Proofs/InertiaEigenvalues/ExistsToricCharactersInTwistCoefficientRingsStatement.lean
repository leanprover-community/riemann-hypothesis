module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.ToricRational.RatioConj → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (Z : GlobalTheory.LamTie.LamDat D), Z.C = cf → Z.Ok → (∀ a, GlobalTheory.LamTie.TeichTriv D.host (Z.chi a)) → ValLL0 D cf → (∀ a, (Z.chi a).ValuesIn 0 (embLL0 D)) → (∀ i P, (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → P ∈ T.S0 i) → ∃ L : TwL T, ∀ F : TwF T, GlobalTheory.LamTie.IsLamTieFull (T.ntw hE F L) Z ∧ ∀ (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))) (h0 : _) th, Nonempty (SideB (⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) → ∀ th', Nonempty (SideB (⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) := by
  first | exact @GlobalTheory.LamInstall.exists_twL_installed | exact GlobalTheory.LamInstall.exists_twL_installed | (intros; apply GlobalTheory.LamInstall.exists_twL_installed <;> assumption)
