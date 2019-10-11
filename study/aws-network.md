- VPC
  - 0-n subnets
  - 0-1 IG
  - limit: 5 per region (soft)

- Subnets
  - 1 VPC
  - 1 CIDR block (IP range)
  - 1 AZ
  - 1 ACL
  - 1 RT (unspecified => VPC's main RT)
  - limit: 200 per VPC

- Route table : [ip range => target]
  - 1 VPC
  - 0-n subnets
  - Add 0.0.0.0/0 -> IG or NAT for outbound internet
  - limit: 200 per VPC

NAT - internet proxy for private subnets
  - 1 subnet
  - 1 IP

Network ACL = firewall
  - 0-n subnets
  - Specify Allow & Deny
  - No rules = allow everything
  - Second layer of defence
  - Only one can be applied
  - rules are ordered, sequential

Security Group
  - 0-n instances
  - Specify Allow only
  - No rules = allow nothing
  - First layer of defence
  - Multiple can be applied
  - if you open inbound port 80, it will automatically open outbound port 80 as well
  - rules are unordered, monoidal
  - can represent a source/target in other places (eg. a group of instances)
  - limit: 500 per VPC

Elastic IP = static IP
