(* MAC.ec *)

(* Message Authentication Codes *)

(* definitions, including games for judging correctness and EU-CMA
   (Existential Unforgeability under a Chosen Message Attack) security *)

prover [""].  (* no SMT solvers *)

require import AllCore Distr DBool.

(* theory parameters *)

type key.  (* tagging keys *)

type text.  (* plaintexts *)

type tag.  (* tags *)

op tag_def : tag.  (* default tagtext *)

(* MAC oracle limit before game's MAC
   this says limit_pre has type int and the axiom ge0_limit_pre says
   limit_pre is non-negative *)
op limit_pre : {int | 0 <= limit_pre} as ge0_limit_pre.
(* MAC oracle limit after game's MAC *)
op limit_post : {int | 0 <= limit_post} as ge0_limit_post.

(* end theory parameters *)

(* module type of MAC schemes

   an MAC scheme Mac should be stateless, meaning that

     forall (g1 g2 : glob Mac), g1 = g2 *)

module type MAC = {
  (* key generation *)
  proc key_gen() : key

  (* Tagging *)
  proc tag(k : key, x : text) : tag

  (* Verifying *)
  proc ver(k : key, t : tag, x : text) : bool
}.

(* module for checking correctness of a MAC, parameterized
   by MAC scheme

   correctness means main returns true with probability 1, without any
   assumptions about value of x *)

module Cor (Mac : MAC) = {
  proc main(x : text) : bool = {
    var k : key; var t : tag; var y : bool;
    k <@ Mac.key_gen();
    t <@ Mac.tag(k, x);
    y <@ Mac.ver(k, t, x);
    return y;
  }
}.

(* module type of MAC oracles *)

module type MO = {
  (* initialization *)
  proc * init() : unit

  (* tagging of text by adversary before game's tagging *)
  proc tag_pre(x : text) : tag
  (* one-time tag of text by game *)
  proc gtag(x : text) : tag
  (* tagging of text by adversary after game's tagging *)
  proc tag_post(x : text) : tag
}.

(* standard MAC oracle, constructed from an MAC
   scheme *)

module MacO (Mac : MAC) : EO = {
  var key : key
  var ctr_pre : int
  var ctr_post : int

  proc init() : unit = {
    key <@ Mac.key_gen();
    ctr_pre <- 0; ctr_post <- 0;
  }

  proc mac_pre(x : text) : tag = {
    var t : tag;
    if (ctr_pre < limit_pre) {
      ctr_pre <- ctr_pre + 1;
      t <@ Mac.tag(key, x);
    }
    else {
      t <- tag_def;  (* default result *)
    }  
    return t;
  }

  proc gtag(x : text) : tag = {
    var t : tag;
    t <@ Mac.tag(key, x);
    return t;
  }

  proc tag_post(x : text) : tag = {
    var t : tag;
    if (ctr_post < limit_post) {
      ctr_post <- ctr_post + 1;
      t <@ Mac.tag(key, x);
    }
    else {
      t <- ciph_def;  (* default result *)
    }  
    return t;
  }
}.

(* MAC adversary, parameterized by encryption oracle, MO

   choose may only call MO.tag_pre; guess may only call MO.tag_post *)

module type ADV (MO : MO) = {
  (* choose a pair of plaintexts, x1/x2 *)
  proc * choose() : text * text {MO.tag_pre}

  (* given tag t based on a random boolean b (the encryption
     using EO.genc of x1 if b = true, the encryption of x2 if b =
     false), try to guess b *)
  proc guess(c : tag) : bool {MO.tag_post}
}.

(* IND-CPA security game, parameterized by an encryption scheme Enc
   and adversary Adv

   an encryption scheme is secure iff the probability of main
   returning true (Adv winning the game) is close to 1/2, i.e., Adv
   isn't doing much better than always guessing the ciphertext comes
   from the first plaintext, or of making a random guess

   formally, we want that the absolute value of the difference between
   the probability that main returns true and 1/2 to be small; this
   says that Adv can neither win nor lose with probability much
   different than 1/2 (if it could reliably lose, the addition of
   a negation would result in an adversary that could reliably win)

   because Adv can use EO to encrypt the plaintexts it chooses,
   the encryption procedure of a secure encryption scheme is
   necessarily probabilistic

   Adv may directly use Enc (which is stateless) as much as it wants
   (and in any case could simulate it), but the security theorem must
   say it can't read/write the global variables of EncO *)

module INDCPA (Enc : ENC, Adv : ADV) = {
  module EO = EncO(Enc)        (* make EO from Enc *)
  module A = Adv(EO)           (* connect Adv to EO *)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : tag;
    EO.init();                 (* initialize EO *)
    (x1, x2) <@ A.choose();    (* let A choose plaintexts x1/x2 *)
    b <$ {0,1};                (* choose boolean b *)
    c <@ EO.genc(b ? x1 : x2); (* encrypt x1 if b = true, x2 if b = false *)
    b' <@ A.guess(c);          (* give ciphertext to A, which returns guess *)
    return b = b';             (* see if A guessed correctly, winning game *)
  }
}.