import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthDataExistsAtPointsProof
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthDataExistsAtPointsProof
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimeDepthDataExistsAtPointsProof
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PackagesExistFrobeniusComplexConjugation
import Development.AutomorphicArithmetic.OrbitLabellings.ExistsPkgCsOfDegreeBoundAtInertPrimes

section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem goodPrime_packages :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
        (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _
  exact ⟨GlobalTheory.T.inertPrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).1, GlobalTheory.T.splitPrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c,
    GlobalTheory.T.largePrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).2,
    (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).1, (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).2⟩

end GlobalTheory
end

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allGoodPrimeDepthDataExist_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  atlas_forward_decl GlobalTheory.goodPrime_packages
