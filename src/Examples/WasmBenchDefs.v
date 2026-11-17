From Stdlib Require Import Utf8 ZArith Vector.
From Utility Require Import Zpstar Util.
From Examples Require Import HeliosTallyIns HeliosFrontendIns.
Import Vspace Schnorr Zpfield Zpgroup VectorNotations.

(** * WebAssembly benchmarks at the Helios parameters

    These are fixed inputs for compiling the Helios voting client
    ([Examples/HeliosFrontendIns.v]) to WebAssembly with CertiRocq. The
    terms are a 7-candidate approval ballot at the 2048-bit Helios group of
    [Examples/HeliosTallyIns.v] under the IACR 2024 key [h2024], with
    pinned randomness and challenges so that each compiled term is closed.
    They are compiled by [bench/wasm/WasmBench.v]
    ([CertiRocq Compile Wasm]). The same ballot term is also used by the
    CakeML pipeline in [bench/cakeml/Driver.v].

    According to [bench/README.md], all terms compile, but at 2048 bits the
    vote and ballot modules exhaust the backend's 2 GB linear memory,
    because CertiRocq computes on constructor-represented binary integers
    without garbage collection. Only the small exponentiation probe runs.
    [Examples/WasmBenchSmallDefs.v] repeats the experiment at smaller
    parameters. Nothing is proved here. *)
Section WasmBench.

  (** [q ≠ 0], and [mkzp], which builds field elements from integers by
      reduction mod [q]. *)
  Lemma q_neq_zero : q <> 0%Z.
  Proof. discriminate. Qed.

  Definition mkzp (z : Z) : @Zp q :=
    mk_zp (Z.modulo z q) (Z.mod_mod z q q_neq_zero).

  (** The fixed encryption randomness of the seven answers. *)
  Definition bench_rs : Vector.t (@Zp q) 7 :=
    [mkzp 16157387885063800092468972531095442600227637936690303362357377535130907802014; mkzp 48577076477968534331538798282877345169449379072358607271499506168024290496436; mkzp 24931630262289254097214708091063276378844549758072156217765307150175356726206; mkzp 41566972108330407139236895720128556017787341847205356916185490192885258906212; mkzp 53197766383624673008632826004499831964307484393215164687250509730196370056212; mkzp 33947725049433467350045554180148557448142904607798194645610524279359899319942; mkzp 22265497333554630303189440116913175127723344406891330686641041557895790189875].

  (** The fixed approvals (1, 0, 1, 0, 1, 1, 0). *)
  Definition bench_ms : Vector.t (@Zp q) 7 :=
    [mkzp 1; mkzp 0; mkzp 1; mkzp 0; mkzp 1; mkzp 1; mkzp 0].

  (** The fixed proof randomness (commitment exponents and simulated
      challenge) of each 0-or-1 proof. *)
  Definition bench_uscs : Vector.t (Vector.t (@Zp q) 3) 7 :=
    [[mkzp 52501326164280954343698450070125624996742870340154584073996146161991243611954; mkzp 31257822517213891940509019445600240522420303181573668741565908698740762328578; mkzp 37549375448611606962716670886564817868763826366789923558304100546674531854055];
     [mkzp 57145230364634701078616884652580698479665404788326533747522401390664714493080; mkzp 18524649580344938191987111572137183814485582824836244259728656599794437183193; mkzp 18313416694536509187990553052756707576125682889637264882517364677021497468873];
     [mkzp 43296265856110787529131751065902413139591193992613559471938315149424200179881; mkzp 42030301217962052027888225426271455573524234370981566081610181757278783634130; mkzp 27891024414110720275998855061311818196645931397334558640308875064312239221425];
     [mkzp 43239140249798274522693233226603180763297219761552611527960157819962413458144; mkzp 7413692770183022330263885683119040191059594519308836671134129401019492684706; mkzp 832642807261969651737710755843279206580494383667266661818410112103981303452];
     [mkzp 3637372052788598466420146433043537929916209138616999720534878254835941808727; mkzp 56207159024649998084539578186869177829502164952236387237372748083763902222530; mkzp 10922181505477351522091432875941946094753416179083850468797302868461412743162];
     [mkzp 7018468225341733097758751788831699401447771956569948043173404986782995756827; mkzp 22184614573017316617263561940618923848729756428549446274207641777548714717243; mkzp 53568670938127896908685659506789523802530254123175143793583641106379936204784];
     [mkzp 1708842438543908929142226980949167446672898799427190374644070389338572201636; mkzp 47059533152203304019185608478392141009934122635931479659359222435168398615428; mkzp 19063676143413803408162635089582444044372988309698101793569727251730394184216]].

  (** The fixed challenges of the seven proofs. *)
  Definition bench_cs : Vector.t (@Zp q) 7 :=
    [mkzp 25208041352013350914181268198464660734142939796798633831607970217026268878133; mkzp 36312956789914535582708166909001851179991473707227092547023733987404890854983; mkzp 7934228005399036278662023265740860857293714209765196968217854668541679993574; mkzp 9493029999266133874112142425512529214795730713179986437259810130599562829466; mkzp 30194604598268071226266109628101071928703957961016952184086877097840306442980; mkzp 15154669289319748637946665068896187288438726373453184700330637945559296136377; mkzp 11577038227344506415717883452759411284500659788629987993479326702200243236740].

  (** Encryption and proofs of the full ballot under [h2024]. *)
  Definition helios_wasm_ballot_bench :=
    helios_encrypt_ballot_and_generate_enc_proof h2024 bench_rs bench_ms bench_uscs bench_cs.

  (** Verification of [helios_wasm_ballot_bench] (expected [true]). *)
  Definition helios_wasm_ballot_verify_bench : bool :=
    helios_verify_encryption_ballot_proof h2024 helios_wasm_ballot_bench.

  (** *** Scaled-down probes

      A single 0/1 vote and bare modular exponentiations, which
      characterise the limits of the WebAssembly backend. *)

  (** The inputs of a single vote: the first entry of each fixed input, with
      approval 1. *)
  Definition bench_rs1 : Vector.t (@Zp q) 1 := [Vector.hd bench_rs].
  Definition bench_ms1 : Vector.t (@Zp q) 1 := [mkzp 1].
  Definition bench_uscs1 : Vector.t (Vector.t (@Zp q) 3) 1 := [Vector.hd bench_uscs].
  Definition bench_cs1 : Vector.t (@Zp q) 1 := [Vector.hd bench_cs].

  (** Encryption and proof of the single vote. *)
  Definition helios_wasm_vote_bench :=
    helios_encrypt_ballot_and_generate_enc_proof h2024 bench_rs1 bench_ms1 bench_uscs1 bench_cs1.

  (** One full exponentiation [g^r] with a 256-bit exponent. *)
  Definition helios_wasm_modexp_bench : @Schnorr_group p q :=
    (@pow k p q safe_prime prime_p prime_q) g (Vector.hd bench_rs).

  (** Tiny-exponent probes, [g^3] and [g^65537] (17 modular operations),
      which measure the cost of individual operations. Per [bench/README.md],
      the [g^65537] probe is the one that runs in Node at 2048 bits. *)
  Definition helios_wasm_mul_bench : @Schnorr_group p q :=
    (@pow k p q safe_prime prime_p prime_q) g (mkzp 3).
  Definition helios_wasm_modexp16_bench : @Schnorr_group p q :=
    (@pow k p q safe_prime prime_p prime_q) g (mkzp 65537).

End WasmBench.
