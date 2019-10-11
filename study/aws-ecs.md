- Cluster
  - 0-n services

- Service
  - 1 task def
  - 1 cluster
  - task count & placement
  - 0-1 ELB
  - 0-1 Route 53 namespace for "service discovery integration" (?)
  - 0-1 Auto Scaling policy

- Task def
  - docker image & everything else in docker compose (inc volumes, cpu/mem, network etc)

- ALB
  - 0-n subnets

- Target group
  - protocol & port
  - healthcheck

- ALB listener
  - 1 ALB
  - 1 TG
  - protocol & port

- Launch config
  - 1 AMI
  - 1 instance type
  - 0-1 ssh key pair
  - init script

- ASG
  - task count range
  - 1 launch config

- Container instance: an EC2 instance running the ECS agent and registered to a cluster
  - needs the `ecsInstanceRole` IAM role
  - registers with the default cluster by default
  - a specific cluster can be specified by running `echo ECS_CLUSTER={cluster_name} >> /etc/ecs/ecs.config` in the `User data`

--------------------------------------

- Cluster
  - 0-n services
    - task def
      - ELB
        - 0-n listeners
          - 0-1 target groups

- ASG
  - 1 launch config
    - 0-n EC2s
      - 1 ECS agent (optionally with cluster name)
        - 1 cluster

