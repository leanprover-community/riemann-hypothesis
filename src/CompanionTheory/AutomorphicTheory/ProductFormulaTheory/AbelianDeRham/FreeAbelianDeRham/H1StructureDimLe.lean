module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleRestrictCompositeInjectiveCohomologyFo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeExOfAcyclic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExactOfSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsToCoindShortExact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyOfBaseZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HtpyStOfCxSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Pull1RestrictPairRestriction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QIsoAtRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinOfBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalKrullDimLeOfSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero

@[expose] public section

namespace MainStatements.Hodge.Free

theorem h1Le : CompanionTheory.ObstructionTrivialLocus.H1StructureDimLe := by
  have hCx := GlobalTheory.CompanionTheory.HodgeCx.cxSt
  have hDict := GlobalTheory.CompanionTheory.Dict.dictSt
  have hLow := GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt hDict
  have hHtpy := GlobalTheory.CompanionTheory.Hodge.htpySt_of_cxSt hCx
  have hQ := GlobalTheory.CompanionTheory.QCalc.qCalcSt hCx
  have hFub := GlobalTheory.CompanionTheory.NerveCoh.fubiniSt hCx
  have hAff := GlobalTheory.CompanionTheory.AffAcyc.main hCx hHtpy
  have hDesc := GlobalTheory.CompanionTheory.Descent.descentSt hCx hHtpy hQ hFub hAff
  have hBC := GlobalTheory.CompanionTheory.SysBC.sysBCSt hDesc hLow
  have hStein := GlobalTheory.CompanionTheory.Hodge.stein_holds
  have hAx := GlobalTheory.CompanionTheory.Axis.axOSt hDesc hLow hBC hStein
  have hVan := GlobalTheory.CompanionTheory.Hodge.vanSt hCx (GlobalTheory.CompanionTheory.Hodge.Nerve.cmpSt_of_cxSt hCx)
  have hHopf := GlobalTheory.CompanionTheory.HopfSys.hopfSt hHtpy hQ hFub hAff hDesc hLow hAx
  have hHopfLe := GlobalTheory.CompanionTheory.HopfLe.hopfLeSt hCx hDict hLow
  classical
  intro k _ A _ g hA hsm
  haveI : AlgebraicGeometry.IsProper A.hom := ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme.proper (self := hA)
  haveI : CompactSpace A.left := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨P, _, _, ⟨S⟩⟩ := GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys A.hom
  have hfield : IsField k := Field.toIsField k
  have hq : MainStatements.Hodge.AllQIso (MainStatements.Hodge.resSys A.hom S) := hDesc k A.left A.hom inferInstance P S
  obtain ⟨hb1, -, hst⟩ := hLow k _ _ _ _ (MainStatements.Hodge.resSys A.hom S) hq
  have hstein : MainStatements.Hodge.Stein (MainStatements.Hodge.OSys A.hom S) := hst.mp (hStein k A g hA hsm)
  have hexact := hVan k A g hA hsm hfield P S
  have hhopf : MainStatements.Hodge.Hopf (MainStatements.Hodge.OSys A.hom S) True := by
    have h := hHopf k A g hA hsm P S
    rwa [eq_true hfield] at h
  have hno := hHopfLe k P (MainStatements.Hodge.OSys A.hom S) g hfield hstein hexact hhopf
  have hn : ∀ x : Fin (g + 1) → GlobalTheory.CechDR.HO1 A.hom, ¬ LinearIndependent k x := by
    intro x hx
    exact hno (⇑(MainStatements.Hodge.resSys A.hom S).pull1 ∘ x)
      (hx.map' (MainStatements.Hodge.resSys A.hom S).pull1 (LinearMap.ker_eq_bot.mpr hb1.1))
  let b := Module.Basis.ofVectorSpace k (GlobalTheory.CechDR.HO1 A.hom)
  have hemb : ∀ e : Fin (g + 1) ↪ Module.Basis.ofVectorSpaceIndex k (GlobalTheory.CechDR.HO1 A.hom), False :=
    fun e => hn _ (b.linearIndependent.comp e e.injective)
  haveI : Finite (Module.Basis.ofVectorSpaceIndex k (GlobalTheory.CechDR.HO1 A.hom)) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hemb (Fin.valEmbedding.trans (Infinite.natEmbedding _))
  haveI hfin : Module.Finite k (GlobalTheory.CechDR.HO1 A.hom) := Module.Finite.of_basis b
  refine ⟨hfin, ?_⟩
  rw [Module.finrank_eq_nat_card_basis b]
  by_contra hlt
  rw [not_le] at hlt
  exact hemb ((Fin.castLEEmb (Nat.succ_le_of_lt hlt)).trans (Finite.equivFin _).symm.toEmbedding)

end MainStatements.Hodge.Free
