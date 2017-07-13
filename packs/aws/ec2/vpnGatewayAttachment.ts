// *** WARNING: this file was generated by the Lumi Terraform Bridge (TFGEN) Tool. ***
// *** Do not edit by hand unless you're certain you know what you are doing! ***

import * as lumi from "@lumi/lumi";

export class VpnGatewayAttachment extends lumi.NamedResource implements VpnGatewayAttachmentArgs {
    public readonly vpcId: string;
    public readonly vpnGatewayId: string;

    constructor(name: string, args: VpnGatewayAttachmentArgs) {
        super(name);
        this.vpcId = args.vpcId;
        this.vpnGatewayId = args.vpnGatewayId;
    }
}

export interface VpnGatewayAttachmentArgs {
    readonly vpcId: string;
    readonly vpnGatewayId: string;
}
