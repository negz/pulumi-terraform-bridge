// *** WARNING: this file was generated by the Lumi Terraform Bridge (TFGEN) Tool. ***
// *** Do not edit by hand unless you're certain you know what you are doing! ***

import * as lumi from "@lumi/lumi";

export class SshKey extends lumi.NamedResource implements SshKeyArgs {
    public readonly encoding: string;
    public readonly fingerprint?: string;
    public readonly publicKey: string;
    public readonly sshPublicKeyId?: string;
    public readonly status?: string;
    public readonly username: string;

    constructor(name: string, args: SshKeyArgs) {
        super(name);
        this.encoding = args.encoding;
        this.fingerprint = args.fingerprint;
        this.publicKey = args.publicKey;
        this.sshPublicKeyId = args.sshPublicKeyId;
        this.status = args.status;
        this.username = args.username;
    }
}

export interface SshKeyArgs {
    readonly encoding: string;
    readonly fingerprint?: string;
    readonly publicKey: string;
    readonly sshPublicKeyId?: string;
    readonly status?: string;
    readonly username: string;
}
