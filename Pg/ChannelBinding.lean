module

public section

namespace Pg

/-- libpq-compatible SCRAM channel-binding policy. -/
inductive ChannelBindingMode where
  /-- Use SCRAM-SHA-256-PLUS whenever TLS and server support permit it. -/
  | prefer
  /-- Refuse connections that cannot authenticate with channel binding. -/
  | require
  /-- Never negotiate SCRAM-SHA-256-PLUS. -/
  | disable
  deriving Repr, BEq, Inhabited

/-- Actionable channel-binding policy and mechanism-advertisement failures. -/
inductive ChannelBindingFailure where
  /-- No TLS channel exists, so `tls-server-end-point` cannot be constructed. -/
  | tlsRequired
  /-- TLS exists, but authentication cannot select SCRAM-SHA-256-PLUS. -/
  | plusNotOffered
  /-- A server advertised a TLS-only mechanism on a plaintext connection. -/
  | plusWithoutTls
  deriving Repr, BEq, Inhabited

namespace ChannelBindingFailure

def toMessage : ChannelBindingFailure → String
  | .tlsRequired => "channel_binding=require requires TLS"
  | .plusNotOffered =>
    "channel_binding=require requires SCRAM-SHA-256-PLUS, but the server did not offer it"
  | .plusWithoutTls =>
    "server advertised SCRAM-SHA-256-PLUS without TLS"

end ChannelBindingFailure

instance : ToString ChannelBindingFailure := ⟨ChannelBindingFailure.toMessage⟩

end Pg
